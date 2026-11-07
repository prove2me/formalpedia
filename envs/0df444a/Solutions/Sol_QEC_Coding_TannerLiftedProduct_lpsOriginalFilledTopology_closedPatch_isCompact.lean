-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_closedPatch_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:46:52.245433+00:00
-- url     : https://prove2.me/submissions/000adb1f-dc1e-4521-898a-85b3466522b2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspClosedPatch_disc_inside


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @IsCompact (LPSOriginalFilledCurve N) (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspClosedPatch N c) := by
  let := lpsOriginalFilledTopology N
  have hc : ContinuousOn
      (lpsOriginalFilledCuspInvFun N (lpsOriginalCuspRepresentative N c))
      (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target :=
    continuousOn_iff_continuous_domRestrict.mpr (lpsOriginalFilledTopology_param_continuous N c)
  exact (isCompact_closedBall (0:ℂ) _).image_of_continuousOn
    (hc.mono (lpsOriginalFilledCuspClosedPatch_disc_inside N c))
end QEC.Coding.TannerLiftedProduct
