-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_original_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:42.420184+00:00
-- url     : https://prove2.me/submissions/42a97f65-c175-437f-9342-2630e0e29313

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
    (s : Set ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)) :
    (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) ⁻¹'
      (lpsOriginalFilledCuspParam N c '' s)=
        lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) ''
          (lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) ⁻¹' s) := by
  ext x
  constructor
  · rintro ⟨q,hq,he⟩
    by_cases hz : q.val=0
    · rw [lpsOriginalFilledCuspParam_zero N c q hz] at he
      cases he
    · let q' : lpsOriginalCuspDisk N (lpsOriginalCuspRepresentative N c) := ⟨q.val,hz,q.property⟩
      have hp : lpsOriginalFilledCuspParam N c q=
          Sum.inl (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q') :=
        lpsOriginalFilledCuspParam_punct N c q'
      rw [hp] at he
      exact ⟨q',hq,Sum.inl.inj he⟩
  · rintro ⟨q,hq,he⟩
    refine ⟨lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) q,hq,?_⟩
    rw [lpsOriginalFilledCuspParam_punct,he]
end QEC.Coding.TannerLiftedProduct
