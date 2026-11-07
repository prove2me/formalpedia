-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_param_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:20.39388+00:00
-- url     : https://prove2.me/submissions/b1245ec0-c88b-4818-bf10-3a811c7af273

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @Continuous _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspParam N c) := by
  apply continuous_iff_coinduced_le.mpr
  exact (le_iSup (fun c => TopologicalSpace.coinduced (lpsOriginalFilledCuspParam N c)
    inferInstance) c).trans le_sup_right
end QEC.Coding.TannerLiftedProduct
