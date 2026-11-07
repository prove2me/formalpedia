-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:16.933277+00:00
-- url     : https://prove2.me/submissions/d08d99d0-37b1-4f01-ac67-1f67d9056886

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
theorem _root_.solution (N : ℕ) [NeZero N] :
    @Continuous _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by
  apply continuous_iff_coinduced_le.mpr
  exact le_sup_left
end QEC.Coding.TannerLiftedProduct
