-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeBranch_finite_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:40:05.213146+00:00
-- url     : https://prove2.me/submissions/47ddf4ab-41b0-4319-8b76-2899ea64c66f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_finite_action


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] (m : Fin p) (τ : ℍ) :
    ((lpsHeckeUpperGL ℝ p (some m) • τ:ℍ):ℂ)=
      ((τ:ℂ)+(m.val:ℂ))/(p:ℂ) :=
  lpsHeckeUpperGL_finite_action p m τ
end QEC.Coding.TannerLiftedProduct
