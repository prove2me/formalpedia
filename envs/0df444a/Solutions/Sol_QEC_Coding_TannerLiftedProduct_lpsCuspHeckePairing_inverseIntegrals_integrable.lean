-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_inverseIntegrals_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:48:25.14179+00:00
-- url     : https://prove2.me/submissions/bd990e11-b380-40c9-b237-9f5dd0a5b98f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoInversePetersson_image_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_det


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : Option (Fin p)) :
    IntegrableOn (petersson 2 f (g ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p i)⁻¹))
      ((lpsHeckeUpperGL ℝ p i) • lpsGamma0PeterssonDomain N) volume := by
  apply lpsWeightTwoInversePetersson_image_integrable N f g
  rw [lpsHeckeUpperGL_det]
  exact_mod_cast (Fact.out : p.Prime).pos
end QEC.Coding.TannerLiftedProduct
