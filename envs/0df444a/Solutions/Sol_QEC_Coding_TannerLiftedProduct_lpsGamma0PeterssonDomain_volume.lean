-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:04:39.131045+00:00
-- url     : https://prove2.me/submissions/cb6f6024-e1f4-497e-9e96-b3155728369e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0CosetSection_mk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCosetSectionDomain_volume
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveGamma0_index
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Domain_finiteIndex


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    (volume : Measure ℍ) (lpsGamma0PeterssonDomain N) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * volume ModularGroup.fd := by
  let : (lpsEffectiveGamma0 N).FiniteIndex := lpsGamma0Domain_finiteIndex N
  rw [lpsGamma0PeterssonDomain,lpsCosetSectionDomain_volume _ _ (lpsGamma0CosetSection_mk N),lpsEffectiveGamma0_index]
end QEC.Coding.TannerLiftedProduct
