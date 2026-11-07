-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspChart_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:00:37.77949+00:00
-- url     : https://prove2.me/submissions/c0383857-ed77-45a7-9270-534eae11b3b1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    (lpsOriginalFilledCuspChart N c).source=
      lpsOriginalFilledCuspSource N (lpsOriginalCuspRepresentative N c) := rfl
end QEC.Coding.TannerLiftedProduct
