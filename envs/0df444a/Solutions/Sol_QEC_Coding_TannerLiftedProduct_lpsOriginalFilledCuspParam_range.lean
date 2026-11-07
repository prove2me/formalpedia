-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:43:36.655514+00:00
-- url     : https://prove2.me/submissions/9f6e596e-bbd4-4126-8f8a-3e76c199b319

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_mem_source

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    Set.range (lpsOriginalFilledCuspParam N c)=
      (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).source := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    exact lpsOriginalFilledCuspParam_mem_source N c q
  · intro hx
    let e := lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)
    refine ⟨⟨e x,e.map_source hx⟩,?_⟩
    exact e.left_inv hx
end QEC.Coding.TannerLiftedProduct
