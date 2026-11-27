-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_PolyOfDiffsExact_full_22251d1276d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:25.738237+00:00
-- url     : https://prove2.me/submissions/47214e3c-e8a0-464b-9549-cb2ed307ab2e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsPolyBackDiffPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_mvpoly_backDiff_96559c510566

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace PolyOfDiffsExact
theorem _root_.solution : PolyOfDiffsExact.Statement := by
  intro K _ _ h hq
  choose q hq using hq
  choose R hR using fun k => exists_mvpoly_backDiff k (q k)

  have step : ∀ k (m : K → ℤ) (t : ℤ),
      h (Function.update m k t) - eval (fun j => ((Function.update m k t j : ℤ) : ℚ)) (R k) =
        h (Function.update m k (t - 1)) - eval (fun j => ((Function.update m k (t - 1) j : ℤ) : ℚ)) (R k) := by
    intro k m t
    have e1 := hq k (Function.update m k t)
    have e2 := hR k (fun j => ((Function.update m k t j : ℤ) : ℚ))
    have s : Function.update m k t - Pi.single k 1 = Function.update m k (t - 1) := by
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj]
    have s' : (fun j => ((Function.update m k t j : ℤ) : ℚ)) - Pi.single k 1 =
        fun j => ((Function.update m k (t - 1) j : ℤ) : ℚ) := by
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj]
    rw [s] at e1
    rw [s'] at e2
    linear_combination e1 - e2
  have line : ∀ k (m : K → ℤ) (t : ℤ),
      h (Function.update m k t) - eval (fun j => ((Function.update m k t j : ℤ) : ℚ)) (R k) =
        h (Function.update m k 0) - eval (fun j => ((Function.update m k 0 j : ℤ) : ℚ)) (R k) := by
    intro k m t
    induction t using Int.induction_on with
    | zero => rfl
    | succ i ih => rw [step, add_sub_cancel_right, ih]
    | pred i ih => rw [← ih, step k m (-(i : ℤ))]
  have key : ∀ s : Finset K, ∃ p : MvPolynomial K ℚ, ∀ m : K → ℤ, (∀ j ∉ s, m j = 0) →
      h m = eval (fun j => (m j : ℚ)) p := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨C (h 0), fun m hm => ?_⟩
      rw [eval_C]
      congr 1
      funext j
      exact hm j (Finset.notMem_empty j)
    | insert k s hk ih =>
      obtain ⟨p, hp⟩ := ih
      let z : K → MvPolynomial K ℚ := fun j => if j = k then 0 else X j
      refine ⟨bind₁ z p + R k - bind₁ z (R k), fun m hm => ?_⟩
      have hm0 : ∀ j ∉ s, Function.update m k 0 j = 0 := by
        intro j hj
        by_cases hjk : j = k
        · subst hjk; simp
        · rw [Function.update_of_ne hjk]
          exact hm j (by simp [hjk, hj])
      have hz : ∀ P : MvPolynomial K ℚ, eval (fun j => (m j : ℚ)) (bind₁ z P) =
          eval (fun j => ((Function.update m k 0 j : ℤ) : ℚ)) P := by
        intro P
        induction P using MvPolynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p j hp =>
          simp only [map_mul, hp, bind₁_X_right, eval_X]
          by_cases hj : j = k
          · subst hj; simp [z]
          · simp [z, hj]
      have e := line k m (m k)
      rw [Function.update_eq_self] at e
      rw [map_sub, map_add, hz, hz, ← hp _ hm0]
      linear_combination e
  obtain ⟨p, hp⟩ := key Finset.univ
  exact ⟨p, fun m => hp m (fun j hj => absurd (Finset.mem_univ j) hj)⟩
end PolyOfDiffsExact
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
