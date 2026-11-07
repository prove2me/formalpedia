-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspAffineBranch_nome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:45:08.932425+00:00
-- url     : https://prove2.me/submissions/01377765-ff8b-4098-99ff-dda9b35f936b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedNomeEval_function
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedNomeEval_invParameter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_pullback


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0<m) (r : ℚ) (τ : ℍ) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ (lpsOriginalAnalyticCuspAffineBranch m hm r)=
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm (r:ℝ) • τ) := by
  rw [lpsOriginalAnalyticCuspAffineBranch,map_mul,map_pow,
    lpsOriginalAnalyticCuspLocalizedNomeEval_invParameter,
    lpsOriginalAnalyticCuspLocalizedNomeEval_function]
  change (Function.Periodic.qParam 1 (τ:ℂ))⁻¹^m *
    lpsOriginalClearedAffineCusp m m r (Function.Periodic.qParam 1 (τ:ℂ))=_
  rw [lpsOriginalClearedAffineCusp_pullback m m hm le_rfl r τ,
    ←mul_assoc,←mul_pow,inv_mul_cancel₀ (Function.Periodic.qParam_ne_zero (τ:ℂ)),
    one_pow,one_mul]
end QEC.Coding.TannerLiftedProduct
