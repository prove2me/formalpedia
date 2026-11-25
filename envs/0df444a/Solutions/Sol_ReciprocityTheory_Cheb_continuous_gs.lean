-- Prove2me | solution 1 for ReciprocityTheory.Cheb.continuous_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:22.015728+00:00
-- url     : https://prove2.me/submissions/54cc256a-0631-4080-a131-1012cfb147c0

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Theorems.Thm_ReciprocityTheory_Cheb_gs_eq_ofReal
import Theorems.Thm_ReciprocityTheory_Cheb_uphi_of_norm_eq_zero


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
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (x : mixedSpace E) :
    Continuous fun s : ℝ => Gs χ s x := by
  simp_rw [gs_eq_ofReal]
  by_cases h : mixedEmbedding.norm x = 0
  · simp only [uphi_of_norm_eq_zero h, zero_mul, Complex.ofReal_zero, mul_zero]
    exact continuous_const
  · refine continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul ?_))
    exact (Real.continuous_const_rpow h).comp continuous_neg
end ReciprocityTheory.Cheb
