-- Prove2me | solution 1 for StableMSR.Recovery.FewBallRows.exact_recovery_with_few_large_clusters
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T23:38:55.440382+00:00
-- url     : https://prove2.me/submissions/ce44dd4b-1413-40b3-8543-997eaffe1e4f

import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_cartesian_row_machine
import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_cartesian_rows_certify_partitions
import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_singleton_cover_machine
import Theorems.Thm_StableMSR_Recovery_OracleQueries_point_output_loop
import Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_selector_expression
import Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_cheapest_cover_recovers
import Theorems.Thm_StableMSR_Recovery_Compiler_compiler_execution_exact
import Theorems.Thm_StableMSR_Recovery_FewBallRows_append_few_large_recovery
import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private def setup (B : ℕ) := Cmd.seq (.atom (.integerLoad 0 2)) (.seq (.atom (.pointerConst 1 1))
  (.seq (.atom (.integerLoad 1 1)) (.atom (.pointerConst 2 B))))
private def reset := Cmd.seq (.atom (.pointerConst 0 0)) (.seq (.atom (.pointerConst 1 0)) (.atom (.pointerConst 2 0)))
private lemma prepare {n : ℕ} (d : Point n→Point n→ℝ) (k B : ℕ) :
    ∃s,Executes d (setup B) (initialStore n k) s 4 ∧ s.ptrs 0=(n:ℤ) ∧
      s.ptrs 1=(k:ℤ) ∧ s.ptrs 2=(B:ℤ) ∧ Executes d reset s (initialStore n k) 3 := by
  let s := (Op.pointerConst 2 B).eval d ((Op.integerLoad 1 1).eval d ((Op.pointerConst 1 1).eval d
    ((Op.integerLoad 0 2).eval d (initialStore n k))))
  let t := (Op.pointerConst 2 0).eval d ((Op.pointerConst 1 0).eval d ((Op.pointerConst 0 0).eval d s))
  have endState : t=initialStore n k := by
    dsimp [t,s,Op.eval,initialStore]
    congr 1
    funext j
    by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;> simp [Function.update,h0,h1,h2]
  refine ⟨s,.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))),?_,?_,?_,?_⟩
  all_goals try solve | simp [s,Op.eval,initialStore,Function.update]
  rw [← endState]
  exact .seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))

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

private lemma catalog : ∃a b : ℕ,0 < a ∧ 0 < b ∧ ∀h : ℕ,∃cmd : Cmd,
    ∀(n k : ℕ) (d : Point n→Point n→ℝ),1 ≤ k → k ≤ n → IsMetricArray d →
      ∃s z H,Executes d cmd (initialStore n k) s z ∧ z ≤ a*n^(b*(h+1)) ∧ H ≤ a*n^(b*(h+1)) ∧
        let x := worldOf k H d s
        Ready x s ∧ endpoints x ∧ ∀e : ℝ,0 < e → e < 1 → ∀O,Stable d k (1+e) O →
          (largeClusters d O e).card ≤ h → ∃r < H,good x r ∧ score x r ≤ cost d O := by
  obtain ⟨p,extend⟩ := append_few_large_recovery
  obtain ⟨c,D,cp⟩ := capPoly p
  obtain ⟨a,b,apos,bpos,small,allRows⟩ := cartesian_row_machine
  obtain ⟨sA,spos,single,sing⟩ := singleton_cover_machine
  let A := a+sA+c*4^D
  let B := b+2*D+2
  refine ⟨A+20,B,by omega,by dsimp [B];omega,?_⟩
  intro h
  obtain ⟨add,runAdd⟩ := extend h
  let fst := Cond.pointerLE 0 1
  let snd := Cond.pointerLE 1 2
  let empty := Op.pointerConst 2 0
  refine ⟨.seq (setup h) (.ite fst (.seq reset single)
    (.ite snd (.seq reset small) (.seq (.atom empty) add))),?_⟩
  intro n k d hk hn metric
  have np : 1 ≤ n := by omega
  let K := n^(B*(h+1))
  have one : 1 ≤ K := Nat.one_le_pow _ _ np
  have bmin : 2 ≤ B := by dsimp [B];omega
  have nK : n ≤ K := by
    have exp : 1 ≤ B*(h+1) := Nat.mul_pos (by omega) (by omega)
    simpa [K] using Nat.pow_le_pow_right np exp
  have res : A*K+11 ≤ (A+20)*K := by rw [Nat.add_mul A 20 K];omega
  have padding : A*K ≤ (A+20)*K := Nat.mul_le_mul_right _ (by omega)
  have pad1 : K ≤ (A+20)*K := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨s,es,p0,p1,p2,restore⟩ := prepare d k h
  by_cases eq : n=k
  · subst k
    obtain ⟨t,z,ez,tz,rd,ep,gu⟩ := sing n d np metric
    have guard : fst.test s := by change s.ptrs 0 ≤ s.ptrs 1;rw [p0,p1]
    have time : z ≤ A*K := tz.trans (Nat.mul_le_mul (by dsimp [A];omega) nK)
    refine ⟨t,_,1,.seq es (.ite_true guard (.seq restore ez)),?_,one.trans pad1,rd,ep,?_⟩
    · apply le_trans _ res;omega
    · intro e he hlt O ho _;exact gu O ho.1
  · have kn : k < n := by omega
    have guard : ¬fst.test s := by change ¬s.ptrs 0 ≤ s.ptrs 1;rw [p0,p1];omega
    by_cases few : k ≤ h
    · obtain ⟨t,z,ez,tz,rd,pairs'⟩ := allRows n k d hk hn
      have yes : snd.test s := by change s.ptrs 1 ≤ s.ptrs 2;rw [p1,p2];exact_mod_cast few
      have time : z ≤ A*K := tz.trans (Nat.mul_le_mul (by dsimp [A];omega)
        (Nat.pow_le_pow_right np (Nat.mul_le_mul (by dsimp [B];omega) (by omega))))
      have sz : rows n k ≤ K := Nat.pow_le_pow_right np (Nat.mul_le_mul bmin (by omega))
      obtain ⟨ep,cv⟩ := cartesian_rows_certify_partitions (worldOf k (rows n k) d t) np pairs'
      refine ⟨t,_,_,.seq es (.ite_false guard (.ite_true yes (.seq restore ez))),?_,sz.trans pad1,rd,ep,?_⟩
      · apply le_trans _ res;omega
      · intro e he hlt O ho _
        obtain ⟨r,hr,g,pr⟩ := cv O ho.1;exact ⟨r,hr,g,pr.le⟩
    · have no : ¬snd.test s := by change ¬s.ptrs 1 ≤ s.ptrs 2;rw [p1,p2];omega
      let v := empty.eval d s
      let x := worldOf k 0 d v
      have rd : Ready x v := by
        refine ⟨?_,fun _=>rfl⟩
        intro ax;cases ax <;> simp [x,v,empty,worldOf,World.size,Axis.reg,Op.eval,Function.update,p0,p1]
      let F := rows n (h+1)
      obtain ⟨t,z,ez,tz,ready,ends,_,cv⟩ := runAdd x v hk kn (by change h < k;omega) metric rd
      have nF : n ≤ F := by
        simpa [F,rows] using Nat.pow_le_pow_right np (show 1 ≤ 2*(h+1) by omega)
      have fpos : 1 ≤ F := np.trans nF
      have cap : x.cap + rows x.n (h+1) ≤ 4*F := by change n+k+0+1+F ≤ _;omega
      have pp := tz.trans (cp _ (by change 1 ≤ n+k+0+1+F;omega))
      have zF := pp.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left cap D))
      rw [Nat.mul_pow,←Nat.mul_assoc] at zF
      have powF : F^D ≤ K := by
        change (n^(2*(h+1)))^D ≤ n^(B*(h+1))
        rw [←Nat.pow_mul,show 2*(h+1)*D=(2*D)*(h+1) by ring]
        exact Nat.pow_le_pow_right np (Nat.mul_le_mul_right _ (by dsimp [B];omega))
      have time : z ≤ A*K := zF.trans (Nat.mul_le_mul (by dsimp [A];omega) powF)
      have sz : F ≤ K := Nat.pow_le_pow_right np (Nat.mul_le_mul_right _ bmin)
      have ep : endpoints x := by intro r hr;exact False.elim (Nat.not_lt_zero r hr)
      refine ⟨t,_,0+F,.seq es (.ite_false guard (.ite_false no (.seq (.atom _ _) ez))),?_,?_,ready,ends ep,?_⟩
      · apply le_trans _ res;omega
      · simpa using sz.trans pad1
      · intro e he hlt O ho count
        obtain ⟨u,hu,good',cost'⟩ := cv e he hlt O ho count
        exact ⟨0+u,Nat.add_lt_add_left hu _,good',cost'.le⟩
theorem solution : ∃a b : ℕ,0 < a ∧ 0 < b ∧ ∀h : ℕ,∃P : MinSumFPT.Program,DeterministicProgram P ∧
    ∀(n k : ℕ) (d : Point n→Point n→ℝ),1 ≤ k → k ≤ n → IsMetricArray d →
      ∃t ≤ a*n^(b*(h+1)),
        let s := execute P n k d t
        s.halted=true ∧ s.work ≤ a*n^(b*(h+1)) ∧ ValidLabels n k s ∧
          ∀e : ℝ,0 < e → e < 1 → ∀O,Stable d k (1+e) O →
          (largeClusters d O e).card ≤ h → outputPartition n k s=O := by
  obtain ⟨a,b,apos,bpos,make⟩ := catalog
  obtain ⟨p,S,select⟩ := point_output_loop output selector_expression
  obtain ⟨c,D,est⟩ := capPoly p
  refine ⟨a+c*(a+3)^D+1,b*(D+1),by omega,Nat.mul_pos bpos (by omega),?_⟩
  intro h
  obtain ⟨G,gen⟩ := make h
  let cmd := Cmd.seq G S
  obtain ⟨safe,correct⟩ := compiler_execution_exact cmd 0
  refine ⟨compile cmd 0,safe,?_⟩
  intro n k d hk hn metric
  obtain ⟨s,z,H,ez,tz,th,ready,ep,cv⟩ := gen n k d hk hn metric
  let x := worldOf k H d s
  obtain ⟨v,l,el,tl,entries⟩ := select x s ready
  have exec : Executes d cmd (initialStore n k) v (z+l) := .seq ez el
  let st := v.haltedState cmd.size (0+(z+l)+1) 0
  have final : execute (compile cmd 0) n k d (z+l+1)=st := by
    have ini : MinSumFPT.initState n k 0 0=(initialStore n k).state 0 0 := by simp [initialStore,Store.state,MinSumFPT.initState]
    unfold execute MinSumFPT.run;rw [ini];exact correct n d _ v _ exec (fun _=>0) 0
  have total := combineTime a b c D n k H (h+1) z l (by omega) hn bpos (by omega) tz th
    (tl.trans (est x.cap (by unfold World.cap;omega)))
  have data : ∀i < x.n,st.imem (-1-(i:ℤ))=output x i := entries
  obtain ⟨valid,recover⟩ := cheapest_cover_recovers x st hk hn metric ep data
  refine ⟨z+l+1,total,?_⟩
  dsimp only;rw [final]
  refine ⟨rfl,by simpa [st,Store.haltedState,Store.state] using total,valid,?_⟩
  intro e he hlt O ho count
  exact recover (1+e) (by linarith) O ho (cv e he hlt O ho count)
