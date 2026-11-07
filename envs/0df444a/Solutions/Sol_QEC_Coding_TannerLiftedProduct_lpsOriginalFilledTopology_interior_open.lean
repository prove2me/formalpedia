-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_interior_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:44.172773+00:00
-- url     : https://prove2.me/submissions/ada55b9a-789b-4bc3-92d2-10c41bd6e123

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_isOpen_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPunctInverse_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPunctToFull_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_interior_preimage


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] :
    @IsOpenMap _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (Sum.inl : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by
  intro s hs
  apply (lpsOriginalFilledTopology_isOpen_iff N _).mpr
  constructor
  · rw [Set.preimage_image_eq _ Sum.inl_injective]
    exact hs
  · intro c
    rw [lpsOriginalFilledCuspParam_interior_preimage]
    exact lpsOriginalCuspPunctToFull_open N _ _
      ((lpsOriginalCuspPunctInverse_continuous N _).isOpen_preimage s hs)
end QEC.Coding.TannerLiftedProduct
