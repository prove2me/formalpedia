-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_gs_embZ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:28.063912+00:00
-- url     : https://prove2.me/submissions/6747408f-ba26-4463-93ce-1c8a95699fa7

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Theorems.Thm_ReciprocityTheory_Cheb_norm_gs_le
import Theorems.Thm_ReciprocityTheory_Cheb_norm_embZ
import Theorems.Thm_ReciprocityTheory_Cheb_uphi_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) {s : ℝ} (hs : 1 ≤ s) (α : 𝓞 E) :
    ‖Gs χ s (embZ α)‖ ≤ 1 := by
  refine (norm_gs_le χ s _).trans ?_
  have h1 : (mixedEmbedding.norm (embZ α)) ^ (-s) ≤ 1 := by
    rw [norm_embZ]
    by_cases h0 : Algebra.norm ℤ α = 0
    · rw [h0]; simp only [Int.cast_zero, abs_zero]
      rw [Real.zero_rpow (by linarith)]; norm_num
    · apply Real.rpow_le_one_of_one_le_of_nonpos _ (by linarith)
      have : (1 : ℤ) ≤ |Algebra.norm ℤ α| := Int.one_le_abs h0
      exact_mod_cast this
  calc uphi (embZ α) * (mixedEmbedding.norm (embZ α)) ^ (-s) ≤ 1 * 1 :=
        mul_le_mul (uphi_le_one _) h1 (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _) zero_le_one
    _ = 1 := one_mul 1
end ReciprocityTheory.Cheb
