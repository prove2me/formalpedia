-- Prove2me | solution 1 for StableMSR.Recovery.CartesianBallRows.singleton_cover_machine
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:31:01.822714+00:00
-- url     : https://prove2.me/submissions/edb2f13f-3a69-40ac-9fb7-241863da3d20

import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
import Definitions.Def_StableMSR_CartesianBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma oracleFin {n : ℕ} (d : Point n→Point n→ℝ) (i j : Fin n) :
    MinSumFPT.oracleAnswer d (i.val:ℤ) (j.val:ℤ)=d i j := by
  simp [MinSumFPT.oracleAnswer,MinSumFPT.toPoint,i.isLt,j.isLt]

theorem solution : ∃a : ℕ,0 < a ∧ ∃cmd : Cmd,
    ∀ (n : ℕ) (d : Point n→Point n→ℝ),1 ≤ n → IsMetricArray d →
      ∃s z,Executes d cmd (initialStore n n) s z ∧ z ≤ a*n ∧
        let x := worldOf n 1 d s
        Ready x s ∧ endpoints x ∧ ∀O,Feasible Finset.univ n O →
          ∃r < 1,good x r ∧ score x r ≤ cost d O := by
  classical
  let setup := Cmd.seq (.atom (.integerLoad 0 4)) (.seq (.atom (.pointerCopy 1 0)) (.seq (.atom (.pointerConst 2 1))
    (.seq (.atom (.pointerConst 3 3)) (.seq (.atom (.pointerCopy 5 0)) (.atom (.pointerDec 5))))))
  let body := Cmd.seq (.atom (.integerStore 3 4)) (.seq (.atom (.pointerInc 3)) (.seq (.atom (.integerStore 3 4))
    (.seq (.atom (.pointerInc 3)) (.atom (.pointerInc 4)))))
  let guard := Cond.pointerLE 4 5
  refine ⟨16,by decide,.seq setup (.whileDo guard body),?_⟩
  intro n d hn hm
  let st := (Op.pointerDec 5).eval d ((Op.pointerCopy 5 0).eval d ((Op.pointerConst 3 3).eval d ((Op.pointerConst 2 1).eval d
    ((Op.pointerCopy 1 0).eval d ((Op.integerLoad 0 4).eval d (initialStore n n))))))
  have ini : Executes d setup (initialStore n n) st 6 :=
    .seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _)))))
  let A (i : ℕ) (s : Store) := s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(n:ℤ) ∧ s.ptrs 2=1 ∧ s.ptrs 3=3+2*(i:ℤ) ∧
    s.ptrs 4=(i:ℤ) ∧ s.ptrs 5=(n:ℤ)-1 ∧ ∀j < i,s.imem (3+2*(j:ℤ))=(j:ℤ) ∧ s.imem (3+2*(j:ℤ)+1)=(j:ℤ)
  have start : A 0 st := by simp [A,st,Op.eval,Function.update,initialStore]
  have lp : BoundedSum.LoopBound d body guard A n 5 := by
    constructor
    · intro i s hs
      change s.ptrs 4 ≤ s.ptrs 5 ↔ _
      rw [hs.2.2.2.2.1,hs.2.2.2.2.2.1];omega
    · intro i hi s hs
      obtain ⟨p0,p1,p2,p3,p4,p5,mem⟩ := hs
      let v := (Op.pointerInc 4).eval d ((Op.pointerInc 3).eval d ((Op.integerStore 3 4).eval d
        ((Op.pointerInc 3).eval d ((Op.integerStore 3 4).eval d s))))
      refine ⟨v,_,Executes.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _)))),by decide,?_⟩
      dsimp only [A]
      refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
      all_goals try solve | simp [v,Op.eval,Function.update,p0,p1,p2,p3,p4,p5] <;> ring
      intro j hj
      by_cases e : j=i
      · subst j;simp [v,Op.eval,Function.update,p3,p4]
      · have h1 : 3+2*(j:ℤ) ≠ 3+2*(i:ℤ)+1 := by omega
        have h2 : 3+2*(j:ℤ)+1 ≠ 3+2*(i:ℤ) := by omega
        have h3 : 3+2*(j:ℤ) ≠ 3+2*(i:ℤ) := by omega
        have h4 : 3+2*(j:ℤ)+1 ≠ 3+2*(i:ℤ)+1 := by omega
        simpa [v,Op.eval,p3,p4,Function.update_of_ne h1,Function.update_of_ne h2,
          Function.update_of_ne h3,Function.update_of_ne h4] using mem j (by omega)
  obtain ⟨t,c,ec,tc,last⟩ := BoundedSum.bounded_while_execution d body guard A n 5 lp 0 (Nat.zero_le _) st start
  let x := worldOf n 1 d t
  have pair (j : ℕ) (hj : j < n) : center x 0 j=(j:ℤ) ∧ witness x 0 j=(j:ℤ) := by
    simpa [x,worldOf,center,witness,addr] using last.2.2.2.2.2.2 j hj
  refine ⟨t,_,.seq ini ec,by simp only [Nat.sub_zero] at tc;omega,⟨?_,fun _=>rfl⟩,?_,?_⟩
  · intro a;cases a with
    | points => exact last.1
    | blocks => exact last.2.1
    | rows => exact last.2.2.1
  · intro r hr j hj
    have eq : r=0 := by change r < 1 at hr;omega
    subst r;exact ⟨⟨j,hj⟩,⟨j,hj⟩,pair j hj⟩
  · intro O feasible
    obtain ⟨M,hd⟩ := hm
    letI : MetricSpace (Point n) := M
    have rad (j : ℕ) (hj : j < n) : charge x 0 j=0 := by
      unfold charge;rw [(pair j hj).1,(pair j hj).2]
      have hh := oracleFin d (⟨j,hj⟩ : Fin n) ⟨j,hj⟩
      change MinSumFPT.oracleAnswer d (j:ℤ) (j:ℤ)=0
      exact hh.trans ((hd _ _).symm.trans (dist_self _))
    refine ⟨0,by decide,⟨?_,?_⟩,?_⟩
    · intro j hj l hl eq
      rw [(pair j hj).1,(pair l hl).1] at eq
      exact Int.ofNat.inj eq
    · intro i hi;refine ⟨i,hi,?_⟩
      unfold hits charge;rw [(pair i hi).2]
    · have val : score x 0=0 := Finset.sum_eq_zero (fun j hj=>rad j (Finset.mem_range.mp hj))
      rw [val]
      apply Finset.sum_nonneg
      intro C hC
      have nc := feasible.2.1 C hC
      rw [radius,dif_pos nc];apply Finset.le_inf'
      intro u hu
      rw [eccentricity,dif_pos nc]
      apply le_trans _ (Finset.le_sup' _ hu)
      rw [← hd];exact dist_nonneg
