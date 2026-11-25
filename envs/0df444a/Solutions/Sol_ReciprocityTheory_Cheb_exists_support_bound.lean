-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:03.355003+00:00
-- url     : https://prove2.me/submissions/59dbffb0-c7b7-41de-9ea7-48b36e18e756

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Theorems.Thm_ReciprocityTheory_Cheb_exists_logDev_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ ∀ x : mixedSpace E, uphi x ≠ 0 →
    (∀ w : InfinitePlace E, c₀ * ‖x‖ ≤ normAtPlace w x) ∧
      c₀ ^ Module.finrank ℚ E * ‖x‖ ^ Module.finrank ℚ E ≤ mixedEmbedding.norm x := by
  obtain ⟨C, hC0, hC⟩ := exists_logDev_bound (E := E)
  refine ⟨Real.exp (-(2 * C)), Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), fun x hx => ?_⟩
  obtain ⟨hN, hD⟩ := hC x hx
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    lt_of_le_of_ne (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.mp hN w).symm
  have h1 : ∀ w, Real.exp (-(2 * C)) * ‖x‖ ≤ normAtPlace w x := by
    intro w
    obtain ⟨w', -, hw'⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun w => normAtPlace w x)
    rw [norm_eq_sup'_normAtPlace, hw']
    have a := hD w
    have b := hD w'
    rw [abs_le] at a b
    have hl : Real.log (normAtPlace w' x) - 2 * C ≤ Real.log (normAtPlace w x) := by linarith
    calc Real.exp (-(2 * C)) * normAtPlace w' x
        = Real.exp (Real.log (normAtPlace w' x) - 2 * C) := by
          rw [Real.exp_sub, Real.exp_log (hpos w'), Real.exp_neg]; ring
      _ ≤ Real.exp (Real.log (normAtPlace w x)) := Real.exp_le_exp.mpr hl
      _ = normAtPlace w x := Real.exp_log (hpos w)
  refine ⟨h1, ?_⟩
  rw [← mul_pow, mixedEmbedding.norm_apply, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
  exact pow_le_pow_left₀ (by positivity) (h1 w) _
end ReciprocityTheory.Cheb
