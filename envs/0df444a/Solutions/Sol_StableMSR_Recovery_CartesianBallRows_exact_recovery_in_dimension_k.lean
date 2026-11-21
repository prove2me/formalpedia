-- Prove2me | solution 1 for StableMSR.Recovery.CartesianBallRows.exact_recovery_in_dimension_k
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:33:56.998168+00:00
-- url     : https://prove2.me/submissions/ebc4a125-7cf5-443e-b5dc-e7125263e8a2

import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_cartesian_row_machine
import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_cartesian_rows_certify_partitions
import Theorems.Thm_StableMSR_Recovery_OracleQueries_point_output_loop
import Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_selector_expression
import Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_cheapest_cover_recovers
import Theorems.Thm_StableMSR_Recovery_validLabels_feasible
import Theorems.Thm_StableMSR_Recovery_Compiler_compiler_execution_exact
import Definitions.Def_StableMSR_CartesianBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma getFirst (k : ℕ) (P : ℕ→Prop) (h : ∃j < k,P j) :
    ∃j < k,P j ∧ BallCoverCatalog.first k P=(j:ℤ) := by
  classical
  let z := Nat.find h
  have hz : z < k ∧ P z := Nat.find_spec h
  refine ⟨z,hz.1,hz.2,?_⟩
  have iff' (i : ℕ) (hi : i < k) : (P i ∧ ∀l < k,l < i → ¬P l) ↔ i=z := by
    constructor
    · rintro ⟨pi,lo⟩
      exact le_antisymm (le_of_not_gt (fun lt=>lo z hz.1 lt hz.2)) (Nat.find_min' h ⟨hi,pi⟩)
    · rintro rfl
      exact ⟨hz.2,fun l hl lt pl=>Nat.find_min h lt ⟨hl,pl⟩⟩
  unfold BallCoverCatalog.first
  calc
    _ = ∑i ∈ Finset.range k,if i=z then (i:ℤ) else 0 := Finset.sum_congr rfl (fun i hi=>by simp only [iff' i (Finset.mem_range.mp hi)])
    _ = _ := by simp [hz.1]
private lemma oracleFin {n : ℕ} (d : Point n→Point n→ℝ) (i j : Fin n) :
    MinSumFPT.oracleAnswer d (i.val:ℤ) (j.val:ℤ)=d i j := by
  simp [MinSumFPT.oracleAnswer,MinSumFPT.toPoint,i.isLt,j.isLt]
private lemma ownLabel (x : World) {r j i : ℕ} (g : good x r) (hj : j < x.k) (h : center x r j=(i:ℤ)) :
    assigned x r i=(j:ℤ) := by
  have ex : ∃l < x.k,center x r l=(i:ℤ) := ⟨j,hj,h⟩
  obtain ⟨l,hl,he,ans⟩ := getFirst _ _ ex
  rw [assigned,if_pos ex,ans,g.1 l hl j hj (he.trans h.symm)]
private lemma selectLabel (x : World) {r : ℕ} (g : good x r) (hr : r < x.rows) (he : endpoints x)
    (hm : IsMetricArray x.dist) (i : Fin x.n) :
    ∃j : Fin x.k,assigned x r i.val=(j.val:ℤ) ∧ hits x r i.val j.val := by
  by_cases own : ∃j < x.k,center x r j=(i.val:ℤ)
  · obtain ⟨j,hj,ce⟩ := own
    obtain ⟨_,w,_,hw⟩ := he r hr j hj
    obtain ⟨M,hd⟩ := hm
    letI : MetricSpace (Point x.n) := M
    refine ⟨⟨j,hj⟩,ownLabel x g hj ce,?_⟩
    simp only [hits,charge,ce,hw,oracleFin,← hd,dist_self,dist_nonneg]
  · obtain ⟨j,hj,covers,eq⟩ := getFirst _ _ (g.2 i.val i.isLt)
    exact ⟨⟨j,hj⟩,by rw [assigned,if_neg own];exact eq,covers⟩
private lemma decoding (x : World) (s : MinSumFPT.State) (r : ℕ) (hr : r < x.rows) (g : good x r)
    (hm : IsMetricArray x.dist) (ends : endpoints x)
    (hs : ∀i < x.n,s.imem (-1-(i:ℤ))=assigned x r i) :
    ValidLabels x.n x.k s ∧ cost x.dist (outputPartition x.n x.k s) ≤ score x r := by
  classical
  choose c w hc hw using fun j : Fin x.k=>ends r hr j.val j.isLt
  have own (j : Fin x.k) : s.imem (-1-((c j).val:ℤ))=(j.val:ℤ) :=
    (hs _ (c j).isLt).trans (ownLabel x g j.isLt (hc j))
  have labels (i : Fin x.n) : ∃j : Fin x.k,s.imem (-1-(i.val:ℤ))=(j.val:ℤ) ∧ hits x r i.val j.val := by
    obtain ⟨j,eq,h⟩ := selectLabel x g hr ends hm i
    exact ⟨j,(hs _ i.isLt).trans eq,h⟩
  refine ⟨⟨?_,fun j=>⟨c j,own j⟩⟩,?_⟩
  · intro i
    obtain ⟨j,eq,_⟩ := labels i
    rw [eq];exact ⟨Int.natCast_nonneg _,by exact_mod_cast j.isLt⟩
  let F (j : Fin x.k) : Cluster x.n := Finset.univ.filter (fun i=>s.imem (-1-(i.val:ℤ))=(j.val:ℤ))
  have contained (j : Fin x.k) : c j ∈ F j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,own j⟩
  have inject : Function.Injective F := by
    intro j l eq
    have h : c j ∈ F l := eq ▸ contained j
    apply Fin.ext
    exact Int.ofNat.inj ((own j).symm.trans (Finset.mem_filter.mp h).2)
  have bound (j : Fin x.k) : radius x.dist (F j) ≤ charge x r j.val := by
    have non : (F j).Nonempty := ⟨c j,contained j⟩
    rw [radius,dif_pos non]
    apply (Finset.inf'_le _ (contained j)).trans
    rw [eccentricity,dif_pos non]
    apply Finset.sup'_le
    intro i hi
    obtain ⟨l,el,hit⟩ := labels i
    have same : l=j := Fin.ext (Int.ofNat.inj (el.symm.trans (Finset.mem_filter.mp hi).2))
    subst l
    simpa only [hits,hc,oracleFin] using hit
  change (∑ C ∈ Finset.univ.image F,radius x.dist C) ≤ score x r
  rw [Finset.sum_image (fun _ _ _ _ e=>inject e)]
  exact (Finset.sum_le_sum (fun j _=>bound j)).trans_eq
    (Fin.sum_univ_eq_sum_range (charge x r) x.k)
private lemma winner (x : World) (h : ∃r < x.rows,good x r) : ∃r < x.rows,wins x r := by
  classical
  let G := (Finset.range x.rows).filter (good x)
  have ne : G.Nonempty := by obtain ⟨r,hr,g⟩ := h;exact ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,g⟩⟩
  obtain ⟨u,hu,best⟩ := Finset.exists_min_image G (score x) ne
  let E := G.filter (fun v=>score x v=score x u)
  have en : E.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩
  let v := E.min' en
  obtain ⟨vG,vs⟩ := Finset.mem_filter.mp (show v ∈ E from E.min'_mem en)
  obtain ⟨vr,vg⟩ := Finset.mem_filter.mp vG
  refine ⟨v,Finset.mem_range.mp vr,vg,?_⟩
  intro j hj gj
  have jG : j ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,gj⟩
  rcases lt_or_eq_of_le (best j jG) with lt|eq
  · exact Or.inl (vs.trans_lt lt)
  · exact Or.inr ⟨vs.trans eq,E.min'_le _ (Finset.mem_filter.mpr ⟨jG,eq.symm⟩)⟩
private lemma outputWinner (x : World) (r : ℕ) (hr : r < x.rows) (win : wins x r) (i : ℕ) :
    output x i=assigned x r i := by
  classical
  have ex : ∃u < x.rows,good x u := ⟨r,hr,win.1⟩
  rw [output,if_pos ex]
  have uniq (j : ℕ) (hj : j < x.rows) : wins x j ↔ j=r := by
    constructor
    · intro w
      rcases win.2 j hj w.1 with h|⟨h,le⟩ <;> rcases w.2 r hr win.1 with g|⟨g,ge⟩
      · exact False.elim (lt_asymm h g)
      · exact False.elim (ne_of_lt h g.symm)
      · exact False.elim (ne_of_gt g h)
      · exact le_antisymm ge le
    · rintro rfl;exact win
  calc
    _ = ∑j ∈ Finset.range x.rows,if j=r then assigned x j i else 0 :=
      Finset.sum_congr rfl (fun j hj=>by simp only [uniq j (Finset.mem_range.mp hj)])
    _ = _ := by simp [hr]
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
private lemma capPoly (p : Polynomial ℕ) :
    ∃c D : ℕ,∀m : ℕ,1 ≤ m → p.eval m ≤ c*m^D := by
  classical
  let e := p.natDegree+1
  let s := ∑ i ∈ Finset.range e,p.coeff i
  refine ⟨s,e,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑i ∈ Finset.range e,p.coeff i*m^e := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Nat.le_of_lt (Finset.mem_range.mp hi)))
    _ = s*m^e := (Finset.sum_mul ..).symm
private lemma combineTime (a b c D n k H E z l : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hb : 1 ≤ b) (he : 1 ≤ E) (hz : z ≤ a*n^(b*E)) (hh : H ≤ a*n^(b*E))
    (hl : l ≤ c*(n+k+H+1)^D) :
    z+l+1 ≤ (a+c*(a+3)^D+1)*n^((b*(D+1))*E) := by
  let B := n^(b*E)
  have hB : 1 ≤ B := Nat.one_le_pow _ _ hn
  have bn : n ≤ B := by
    change n ≤ n^(b*E)
    have t := Nat.pow_le_pow_right hn (show 1 ≤ b*E by exact Nat.mul_pos hb he)
    simpa using t
  change H ≤ a*B at hh
  change z ≤ a*B at hz
  have cap : n+k+H+1 ≤ (a+3)*B := by rw [Nat.add_mul];omega
  have bound := hl.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left cap D))
  rw [Nat.mul_pow] at bound
  have bd : B^D ≤ B^(D+1) := Nat.pow_le_pow_right hB (by omega)
  have bb : B ≤ B^(D+1) := by
    simpa using Nat.pow_le_pow_right hB (show 1 ≤ D+1 by omega)
  have one : 1 ≤ B^(D+1) := Nat.one_le_pow _ _ hB
  rw [show (b*(D+1))*E=(b*E)*(D+1) by ring,Nat.pow_mul]
  change z+l+1 ≤ (a+c*(a+3)^D+1)*B^(D+1)
  rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
  apply Nat.add_le_add _ one
  apply Nat.add_le_add (hz.trans (Nat.mul_le_mul_left a bb))
  rw [← Nat.mul_assoc] at bound
  exact bound.trans (Nat.mul_le_mul_left _ bd)

theorem solution : ∃a b : ℕ,0 < a ∧ 0 < b ∧ ∃P : MinSumFPT.Program,DeterministicProgram P ∧
    ∀(n k : ℕ) (d : Point n→Point n→ℝ),1 ≤ k → k ≤ n → IsMetricArray d →
      ∃t ≤ a*n^(b*(k+1)),
        let s := execute P n k d t
        s.halted=true ∧ s.work ≤ a*n^(b*(k+1)) ∧ ValidLabels n k s ∧
          Optimal d Finset.univ k (outputPartition n k s) := by
  classical
  obtain ⟨a,b,ha,hb,G,gen⟩ := cartesian_row_machine
  obtain ⟨p,S,write⟩ := point_output_loop output selector_expression
  obtain ⟨c,D,bd⟩ := capPoly p
  let B := b+2
  let cmd := Cmd.seq G S
  obtain ⟨safe,correct⟩ := compiler_execution_exact cmd 0
  refine ⟨a+c*(a+3)^D+1,B*(D+1),by omega,Nat.mul_pos (by dsimp [B];omega) (by omega),compile cmd 0,safe,?_⟩
  intro n k d hk hn hm
  have np : 0 < n := by omega
  obtain ⟨s,z,ez,tz,ready,pp⟩ := gen n k d hk hn
  let H := rows n k
  let x := worldOf k H d s
  obtain ⟨v,l,el,tl,hlabel⟩ := write x s ready
  have exec : Executes d cmd (initialStore n k) v (z+l) := .seq ez el
  let st := v.haltedState cmd.size (0+(z+l)+1) 0
  have final : execute (compile cmd 0) n k d (z+l+1)=st := by
    have ini : MinSumFPT.initState n k 0 0=(initialStore n k).state 0 0 := by simp [initialStore,Store.state,MinSumFPT.initState]
    unfold execute MinSumFPT.run;rw [ini]
    exact correct n d _ v _ exec (fun _=>0) 0
  have tgen : z ≤ a*n^(B*(k+1)) := tz.trans (Nat.mul_le_mul_left a (Nat.pow_le_pow_right np
    (Nat.mul_le_mul_right (k+1) (by dsimp [B];omega))))
  have rowbound : H ≤ n^(B*(k+1)) := Nat.pow_le_pow_right np
    (Nat.mul_le_mul (show 2 ≤ B by dsimp [B];omega) (by omega))
  have count := rowbound.trans (Nat.le_mul_of_pos_left _ ha)
  have total := combineTime a B c D n k H (k+1) z l np hn (by dsimp [B];omega) (by omega) tgen count
    (tl.trans (bd x.cap (by unfold World.cap;omega)))
  obtain ⟨endpts,allRows⟩ := cartesian_rows_certify_partitions x np pp
  have lab : ∀i < x.n,st.imem (-1-(i:ℤ))=output x i := hlabel
  have valid := (cheapest_cover_recovers x st hk hn hm endpts lab).1
  have feasible := validLabels_feasible _ valid
  obtain ⟨r0,h0,g0,c0⟩ := allRows _ feasible
  obtain ⟨r,hr,win⟩ := winner x ⟨r0,h0,g0⟩
  have price := (decoding x st r hr win.1 hm endpts (fun i hi=>(lab i hi).trans (outputWinner x r hr win i))).2
  refine ⟨z+l+1,total,?_⟩
  dsimp only
  rw [final]
  refine ⟨rfl,by simpa [st,Store.haltedState,Store.state] using total,valid,feasible,?_⟩
  intro Q hQ
  obtain ⟨j,hj,good,eq⟩ := allRows Q hQ
  have h := win.2 j hj good
  exact price.trans ((h.elim (fun t=>t.le) (fun t=>t.1.le)).trans_eq eq)
