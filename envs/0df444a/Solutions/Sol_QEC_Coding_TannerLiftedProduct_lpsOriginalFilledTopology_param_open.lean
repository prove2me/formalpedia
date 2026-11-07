-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledTopology_param_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:36.804512+00:00
-- url     : https://prove2.me/submissions/24ff887b-5327-455c-bad9-9f23b4dfcc06

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_isOpen_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPunctInverse_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPunctToFull_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_original_preimage
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_other_preimage


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    @IsOpenMap _ (LPSOriginalFilledCurve N) _ (lpsOriginalFilledTopology N)
      (lpsOriginalFilledCuspParam N c) := by
  intro s hs
  apply (lpsOriginalFilledTopology_isOpen_iff N _).mpr
  constructor
  · rw [lpsOriginalFilledCuspParam_original_preimage]
    exact lpsOriginalCuspPunctInverse_open N _ _
      ((lpsOriginalCuspPunctToFull_continuous N _).isOpen_preimage s hs)
  · intro d
    by_cases hd : d=c
    · subst d
      rw [Set.preimage_image_eq _ (lpsOriginalFilledCuspParam_injective N c)]
      exact hs
    · rw [lpsOriginalFilledCuspParam_other_preimage N c d hd]
      exact isOpen_empty
end QEC.Coding.TannerLiftedProduct
