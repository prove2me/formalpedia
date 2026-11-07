-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_nonzero_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:12.199201+00:00
-- url     : https://prove2.me/submissions/235cca82-00e0-4ef8-a36c-0d8bc958f28d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_punct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspNeighborhoodChart_projection


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hz : q.val≠0) :
    ∃ τ : {τ : ℍ // 1<τ.im},
      lpsOriginalFilledCuspParam N c q=
        Sum.inl (lpsOriginalCuspProjection N (lpsOriginalCuspRepresentative N c) τ) ∧
      q.val=Function.Periodic.qParam
        (lpsOriginalCuspGroup N (lpsOriginalCuspRepresentative N c)).strictWidthInfty τ.val := by
  let r := lpsOriginalCuspRepresentative N c
  let q' : lpsOriginalCuspDisk N r := ⟨q.val,hz,q.property⟩
  obtain ⟨τ,he⟩ := ((lpsOriginalCuspNeighborhoodChart N r).symm q').property
  have hf : lpsOriginalCuspCoordinate N r τ=q' := by
    rw [←lpsOriginalCuspNeighborhoodChart_projection]
    have hsub : (⟨lpsOriginalCuspProjection N r τ,⟨τ,rfl⟩⟩ :
        Set.range (lpsOriginalCuspProjection N r))=(lpsOriginalCuspNeighborhoodChart N r).symm q' :=
      Subtype.ext he
    rw [hsub]
    exact (lpsOriginalCuspNeighborhoodChart N r).apply_symm_apply q'
  refine ⟨τ,?_,(congrArg Subtype.val hf).symm⟩
  have hp := lpsOriginalFilledCuspParam_punct N c q'
  change lpsOriginalFilledCuspParam N c q=Sum.inl
    (((lpsOriginalCuspNeighborhoodChart N r).symm q').val) at hp
  rw [←he] at hp
  exact hp
end QEC.Coding.TannerLiftedProduct
