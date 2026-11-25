-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_logDev_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:25.870805+00:00
-- url     : https://prove2.me/submissions/fbe5a7eb-6cb2-4648-94af-2a7f4a95ebf9

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Theorems.Thm_ReciprocityTheory_Cheb_exists_logMap_bound
import Theorems.Thm_ReciprocityTheory_Cheb_sum_mult_logDev
import Theorems.Thm_ReciprocityTheory_Cheb_abs_lt_one_of_Tent_ne_zero__b0d272


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
theorem _root_.solution : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : mixedSpace E, uphi x ≠ 0 →
    mixedEmbedding.norm x ≠ 0 ∧ ∀ w : InfinitePlace E, |Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := exists_logMap_bound (E := E)
  refine ⟨Fintype.card (InfinitePlace E) * B, by positivity, fun x hx => ?_⟩
  have hN : mixedEmbedding.norm x ≠ 0 := fun h => hx (by simp [uphi, h])
  have hT : Tent (ucoord x) ≠ 0 := by simpa [uphi, hN] using hx
  have hc : ∀ i, |ucoord x i| < 1 := abs_lt_one_of_Tent_ne_zero hT
  refine ⟨hN, fun w => ?_⟩
  set D : InfinitePlace E → ℝ := fun w => Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹ with hD
  have hlm : ∀ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v = (v.1.mult : ℝ) * D v.1 := fun v => rfl
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by
    exact_mod_cast Fintype.card_pos

  have key : |(w.mult : ℝ) * D w| ≤ Fintype.card (InfinitePlace E) * B := by
    by_cases hw : w = w₀
    · rw [hw]
      have h0 := sum_mult_logDev hN
      rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace E)] at h0
      have h1 : ((w₀ : InfinitePlace E).mult : ℝ) * D w₀ = -∑ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v := by
        simp only [hlm]; linarith
      rw [h1, abs_neg]
      calc |∑ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v|
          ≤ ∑ v : {w : InfinitePlace E // w ≠ w₀}, |logMap x v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _v : {w : InfinitePlace E // w ≠ w₀}, B := Finset.sum_le_sum fun v _ => hB x hc v
        _ = Fintype.card {w : InfinitePlace E // w ≠ w₀} * B := by simp
        _ ≤ Fintype.card (InfinitePlace E) * B := by
          gcongr
          exact_mod_cast Fintype.card_subtype_le _
    · have := hB x hc ⟨w, hw⟩
      rw [hlm] at this
      exact this.trans (le_mul_of_one_le_left hB0 hcard)
  have hm : (1 : ℝ) ≤ w.mult := InfinitePlace.one_le_mult
  rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < w.mult)] at key
  calc |D w| ≤ (w.mult : ℝ) * |D w| := le_mul_of_one_le_left (abs_nonneg _) hm
    _ ≤ _ := key
end ReciprocityTheory.Cheb
