-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_logMap_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:25.861452+00:00
-- url     : https://prove2.me/submissions/57d4e0cf-3ace-4512-a13a-1411a7915088

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_P2M_ReciprocityTheory_Cheb_mult_le_two__43f4dc7aa0b5
import Theorems.Thm_ReciprocityTheory_Cheb_abs_log_normAtPlace_sub_le
import Theorems.Thm_ReciprocityTheory_Cheb_abs_log_norm_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
variable {y k : mixedSpace E} {B a : ℝ}
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) (w : {w : InfinitePlace E // w ≠ w₀}) :
    |logMap (y + k) w - logMap y w| ≤ 4 * (2 * B / a) := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.mpr Module.finrank_pos
  have hδ : 0 ≤ 2 * B / a := div_nonneg (by linarith) (by linarith)
  simp only [logMap_apply]
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have h1 := abs_log_normAtPlace_sub_le hB hk ha hy w.1
  have h2 := abs_log_norm_sub_le hB hk ha hy
  have h3 : |Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
      Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹| ≤ 2 * B / a := by
    rw [← sub_mul, abs_mul, abs_of_pos (inv_pos.mpr hd)]
    calc _ ≤ (Module.finrank ℚ E : ℝ) * (2 * B / a) * (Module.finrank ℚ E : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_pos.mpr hd).le
      _ = 2 * B / a := by field_simp
  have h4 : |Real.log (normAtPlace w.1 (y + k)) - Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
      (Real.log (normAtPlace w.1 y) - Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹)| ≤
        2 * (2 * B / a) := by
    have := abs_sub (Real.log (normAtPlace w.1 (y + k)) - Real.log (normAtPlace w.1 y))
      (Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
        Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹)
    calc _ = |Real.log (normAtPlace w.1 (y + k)) - Real.log (normAtPlace w.1 y) -
          (Real.log (mixedEmbedding.norm (y + k)) * (Module.finrank ℚ E : ℝ)⁻¹ -
            Real.log (mixedEmbedding.norm y) * (Module.finrank ℚ E : ℝ)⁻¹)| := by ring_nf
      _ ≤ _ := this
      _ ≤ 2 * (2 * B / a) := by linarith
  calc (mult w.1 : ℝ) * |_| ≤ 2 * (2 * (2 * B / a)) :=
        mul_le_mul (mult_le_two' w.1) h4 (abs_nonneg _) (by norm_num)
    _ = 4 * (2 * B / a) := by ring
end ReciprocityTheory.Cheb
