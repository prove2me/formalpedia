-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_inverseIntegrals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:48:12.197408+00:00
-- url     : https://prove2.me/submissions/eef12708-d813-4fcd-9176-34232dcd702e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHeckePairing_sum_left
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_integral_transfer


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∑i:Option (Fin p), ∫τ in (lpsHeckeUpperGL ℝ p i) • lpsGamma0PeterssonDomain N,
        petersson 2 f (g ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p i)⁻¹) τ := by
  rw [lpsCuspHeckePairing_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  apply lpsWeightTwoPetersson_integral_transfer
  rw [lpsHeckeUpperGL_det]
  exact_mod_cast (Fact.out : p.Prime).pos
end QEC.Coding.TannerLiftedProduct
