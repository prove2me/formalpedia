-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_openEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:17.25822+00:00
-- url     : https://prove2.me/submissions/44f3e54d-f063-455e-a636-7aa9f6966413

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_open

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    @Topology.IsOpenEmbedding _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  exact .of_continuous_injective_isOpenMap (lpsOriginalFilledTopology_interior_continuous N)
    Sum.inl_injective (lpsOriginalFilledTopology_interior_open N)
end QEC.Coding.TannerLiftedProduct
