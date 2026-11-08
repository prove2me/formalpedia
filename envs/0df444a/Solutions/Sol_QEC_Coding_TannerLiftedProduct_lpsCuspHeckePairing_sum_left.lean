-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:09:15.740044+00:00
-- url     : https://prove2.me/submissions/99beb5af-10dc-495e-b42d-c3fb19c12062

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHeckePairing_gamma0Domain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoSlashPetersson_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_sum_left
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
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        petersson 2 (f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) g τ := by
  rw [lpsCuspHeckePairing_gamma0Domain N p hNp f g (lpsGamma0PeterssonDomain_fundamental N)]
  simp_rw [lpsHeckeSlashSum,lpsWeightTwoPetersson_sum_left]
  apply integral_finsetSum
  intro i _
  apply lpsWeightTwoSlashPetersson_integrable N f g
  rw [lpsHeckeUpperGL_det]
  exact_mod_cast (Fact.out : p.Prime).pos
end QEC.Coding.TannerLiftedProduct
