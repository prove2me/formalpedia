-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_proof_8e68944cb141
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:11:52.836288+00:00
-- url     : https://prove2.me/submissions/badc77ff-c412-4fca-be98-d71d6b403957

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_aeval_le_30e9887fa60b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_exists_antideriv_79b005910f02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_totalDegree_freeze_le_431705d6eba7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_eval_aeval_freeze_229813f8641d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
variable {K : Type}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
theorem _root_.solution : PolyOfDiffs.Statement := by
  intro K _ _ h d hq
  choose q hqd hqe using hq
  have hP : ∀ k, ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ d ∧
      ∀ x : K → ℚ, eval x P - eval (x - Pi.single k 1) P = eval x (q k) := by
    intro k
    rcases hqd k with h0 | hlt
    · exact ⟨0, by simp, fun x => by simp [h0]⟩
    · obtain ⟨P, hPd, hPe⟩ := exists_antideriv k (q k)
      exact ⟨P, hPd.trans hlt, hPe⟩
  choose P hPd hPe using hP
  have hqe' : ∀ k, ∀ᶠ m in Filter.atTop,
      ((diffStep (Pi.single k 1) h m : ℤ) : ℚ) = eval (fun j => (m j : ℚ)) (q k) := hqe
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.eventually_all.2 hqe')

  have hstep : ∀ k, ∀ y : K → ℤ, N ≤ y → (h y : ℚ) - eval (fun j => (y j : ℚ)) (P k) =
      (h (y - Pi.single k 1) : ℚ) - eval (fun j => ((y - Pi.single k 1 : K → ℤ) j : ℚ)) (P k) := by
    intro k y hy
    have e1 := hN y hy k
    have e2 := hPe k (fun j => (y j : ℚ))
    have e3 : (fun j => (y j : ℚ)) - Pi.single k 1 = fun j => ((y - Pi.single k 1 : K → ℤ) j : ℚ) := by
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    rw [e3] at e2
    simp only [diffStep] at e1
    push_cast at e1
    linarith

  have hline : ∀ k, ∀ x : K → ℤ, N ≤ x → x k = N k → ∀ t : ℤ, N k ≤ t →
      (h (Function.update x k t) : ℚ) - eval (fun j => (Function.update x k t j : ℚ)) (P k) =
      (h x : ℚ) - eval (fun j => (x j : ℚ)) (P k) := by
    intro k x hx hxk t ht
    induction t, ht using Int.le_induction with
    | base => rw [← hxk, Function.update_eq_self]
    | succ t ht ih =>
      have hy : N ≤ Function.update x k (t + 1) := by
        intro j
        by_cases hj : j = k
        · subst hj; simp; omega
        · simp [hj]; exact hx j
      have hsh : Function.update x k (t + 1) - Pi.single k 1 = Function.update x k t := by
        funext j
        by_cases hj : j = k
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [hstep k _ hy, hsh, ih]

  have key : ∀ s : Finset K, ∃ Q : MvPolynomial K ℚ, Q.totalDegree ≤ d ∧
      ∀ m : K → ℤ, N ≤ m → (h (pathPt N s m) : ℚ) = eval (fun j => (m j : ℚ)) Q := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨C (h N : ℚ), by rw [totalDegree_C]; exact Nat.zero_le _, fun m _ => ?_⟩
      have e : pathPt N ∅ m = N := by funext j; simp [pathPt]
      rw [e, eval_C]
    | insert k s hk ih =>
      obtain ⟨Q, hQd, hQ⟩ := ih
      refine ⟨Q + aeval (freeze (insert k s) (fun j => (N j : ℚ))) (P k) -
        aeval (freeze s (fun j => (N j : ℚ))) (P k), ?_, fun m hm => ?_⟩
      · refine (totalDegree_sub _ _).trans
          (max_le ((totalDegree_add _ _).trans (max_le hQd ?_)) ?_)
        · exact (totalDegree_aeval_le _ (totalDegree_freeze_le _ _) _).trans (hPd k)
        · exact (totalDegree_aeval_le _ (totalDegree_freeze_le _ _) _).trans (hPd k)
      · have hx : N ≤ pathPt N s m := fun j => by
          simp only [pathPt]
          split_ifs
          · exact hm j
          · exact le_rfl
        have hxk : pathPt N s m k = N k := by simp [pathPt, hk]
        have hupd : pathPt N (insert k s) m = Function.update (pathPt N s m) k (m k) := by
          funext j
          by_cases hj : j = k
          · subst hj; simp [pathPt]
          · simp [pathPt, hj]
        have e := hline k (pathPt N s m) hx hxk (m k) (hm k)
        rw [← hupd] at e
        have c1 : ∀ t : Finset K, (fun j => ((pathPt N t m j : ℤ) : ℚ)) =
            fun j => if j ∈ t then (m j : ℚ) else (N j : ℚ) := by
          intro t; funext j; simp only [pathPt]; split_ifs <;> rfl
        rw [map_sub, map_add, eval_aeval_freeze, eval_aeval_freeze, ← hQ m hm, ← c1, ← c1]
        linarith
  obtain ⟨Q, hQd, hQ⟩ := key Finset.univ
  refine ⟨Q, hQd, ?_⟩
  rw [EventuallyPoly, Filter.eventually_atTop]
  refine ⟨N, fun m hm => ?_⟩
  have e : pathPt N Finset.univ m = m := by funext j; simp [pathPt]
  rw [← e]
  exact (hQ m hm).trans (by rw [e])
end GroundTheory.Heights₂.Heights.FieldNumbers.PolyOfDiffs
