-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_param_openEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:01.346206+00:00
-- url     : https://prove2.me/submissions/309039d3-ec93-49c2-b5ac-47df28e47b8f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @Topology.IsOpenEmbedding _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspParam N c) := by
  let := lpsOriginalFilledTopology N
  exact .of_continuous_injective_isOpenMap (lpsOriginalFilledTopology_param_continuous N c)
    (lpsOriginalFilledCuspParam_injective N c) (lpsOriginalFilledTopology_param_open N c)
end QEC.Coding.TannerLiftedProduct
