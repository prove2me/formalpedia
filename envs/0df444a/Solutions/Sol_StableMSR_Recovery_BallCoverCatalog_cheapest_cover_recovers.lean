-- Prove2me | solution 1 for StableMSR.Recovery.BallCoverCatalog.cheapest_cover_recovers
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:28:22.304996+00:00
-- url     : https://prove2.me/submissions/5b1ee58c-c7b9-4fe2-a432-276e33eef5dd

import Theorems.Thm_StableMSR_Recovery_validLabels_feasible
import Definitions.Def_StableMSR_BallCoverCatalog
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial
open StableMSR.Recovery.BallCoverCatalog
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

theorem solution (x : World) (s : MinSumFPT.State) (hk : 1 ≤ x.k) (hn : x.k ≤ x.n)
    (hm : IsMetricArray x.dist) (he : endpoints x)
    (hs : ∀i < x.n,s.imem (-1-(i:ℤ))=output x i) :
    ValidLabels x.n x.k s ∧ ∀ (γ : ℝ),1 ≤ γ → ∀ O,Stable x.dist x.k γ O →
      (∃r < x.rows,good x r ∧ score x r ≤ cost x.dist O) → outputPartition x.n x.k s=O := by
  classical
  by_cases ex : ∃r < x.rows,good x r
  · obtain ⟨r,hr,win⟩ := winner x ex
    obtain ⟨valid,bound⟩ := decoding x s r hr win.1 hm he (fun i hi=>(hs i hi).trans (outputWinner x r hr win i))
    refine ⟨valid,?_⟩
    intro γ hγ O stab cheap
    obtain ⟨j,hj,gj,price⟩ := cheap
    have low : score x r ≤ score x j := ((win.2 j hj gj).elim (fun h=>h.le) (fun h=>h.1.le))
    obtain ⟨M,hd⟩ := hm
    letI : MetricSpace (Point x.n) := M
    have pert : Perturbation x.dist γ x.dist := by
      constructor
      · intro a b;rw [← hd,← hd,dist_comm]
      · intro a b
        refine ⟨le_rfl,?_⟩
        have dn : 0 ≤ x.dist a b := by rw [← hd];exact dist_nonneg
        nlinarith
    have un := stab.2 x.dist pert
    have feas := validLabels_feasible _ valid
    exact un.2 _ ⟨feas,fun Q hQ=>(bound.trans (low.trans price)).trans (un.1.2 Q hQ)⟩
  · have value (i : ℕ) (hi : i < x.n) : s.imem (-1-(i:ℤ))=(if (i:ℤ) < x.k then (i:ℤ) else (x.k:ℤ)-1) := by
      simpa [output,ex] using hs i hi
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro i;rw [value _ i.isLt];split <;> omega
    · intro j
      refine ⟨⟨j.val,lt_of_lt_of_le j.isLt hn⟩,?_⟩
      rw [value _ (lt_of_lt_of_le j.isLt hn)]
      simp [show (j.val:ℤ) < x.k by exact_mod_cast j.isLt]
    · rintro γ hγ O ho ⟨r,hr,g,_⟩
      exact False.elim (ex ⟨r,hr,g⟩)
