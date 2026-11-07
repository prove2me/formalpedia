-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_interior_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:46:48.503778+00:00
-- url     : https://prove2.me/submissions/0c98e1f1-58b4-496c-ac60-b39227974cf3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_punct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (s : Set (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) :
    lpsOriginalFilledCuspParam N c ⁻¹' (Sum.inl '' s)=
      lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) ''
        (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) ⁻¹' s) := by
  ext q
  constructor
  · rintro ⟨x,hx,he⟩
    by_cases hz : q.val=0
    · rw [lpsOriginalFilledCuspParam_zero N c q hz] at he
      cases he
    · let q' : lpsOriginalCuspDisk N (lpsOriginalCuspRepresentative N c) := ⟨q.val,hz,q.property⟩
      have hp : lpsOriginalFilledCuspParam N c q=
          Sum.inl (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q') :=
        lpsOriginalFilledCuspParam_punct N c q'
      rw [hp] at he
      refine ⟨q',?_,Subtype.ext rfl⟩
      change lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q'∈s
      rw [←Sum.inl.inj he]
      exact hx
  · rintro ⟨q',hq',rfl⟩
    exact ⟨lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q',hq',
      (lpsOriginalFilledCuspParam_punct N c q').symm⟩
end QEC.Coding.TannerLiftedProduct
