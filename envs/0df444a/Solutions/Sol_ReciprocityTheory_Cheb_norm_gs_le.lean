-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_gs_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:57.505895+00:00
-- url     : https://prove2.me/submissions/b17c30b7-9d80-4b8b-841f-a465a62957b3

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Theorems.Thm_ReciprocityTheory_Cheb_gs_eq_ofReal
import Theorems.Thm_ReciprocityTheory_Cheb_uphi_nonneg


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
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) :
    ‖Gs χ s x‖ ≤ uphi x * (mixedEmbedding.norm x) ^ (-s) := by
  rw [gs_eq_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _))]
  exact mul_le_of_le_one_left (mul_nonneg (uphi_nonneg x) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg x) _))
    (DirichletCharacter.norm_le_one χ _)
end ReciprocityTheory.Cheb
