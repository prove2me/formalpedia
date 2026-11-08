-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:08:16.525071+00:00
-- url     : https://prove2.me/submissions/e6d0aaea-d87e-4115-8776-daea27c3d8c0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_sum_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoSlashPetersson_right_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_gamma0Domain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_fundamental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_det


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g) =
      ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        petersson 2 f (g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) τ := by
  rw [lpsCuspPeterssonPairing_gamma0Domain N f (lpsCuspHeckeLinearMap N p hNp g)
    (lpsGamma0PeterssonDomain_fundamental N)]
  change (∫τ in lpsGamma0PeterssonDomain N,petersson 2 f (∑i,g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) τ) = _
  simp_rw [lpsWeightTwoPetersson_sum_right]
  apply integral_finsetSum
  intro i _
  apply lpsWeightTwoSlashPetersson_right_integrable N f g
  rw [lpsHeckeUpperGL_det]
  exact_mod_cast (Fact.out : p.Prime).pos
end QEC.Coding.TannerLiftedProduct
