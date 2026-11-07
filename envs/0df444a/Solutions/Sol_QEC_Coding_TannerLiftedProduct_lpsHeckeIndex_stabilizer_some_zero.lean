-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIndex_stabilizer_some_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:33:33.176203+00:00
-- url     : https://prove2.me/submissions/d8d007ad-6f96-4b4c-b1da-a99d395a7841

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
import Mathlib.GroupTheory.GroupAction.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetAction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightIndex_some_zero_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) :
    letI := lpsHeckeIndexAction N p hNp
    MulAction.stabilizer (CongruenceSubgroup.Gamma0 N)
      (some ⟨0,(Fact.out:p.Prime).pos⟩:Option (Fin p)) =
      (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N) := by
  let := lpsHeckeIndexAction N p hNp
  ext γ
  change lpsHeckeRightIndex N p hNp (γ:SL(2,ℤ))⁻¹ _ _ = _ ↔
    (γ:SL(2,ℤ)) ∈ lpsHeckeConjugateIntersection N p
  rw [lpsHeckeRightIndex_some_zero_iff]
  exact inv_mem_iff
end QEC.Coding.TannerLiftedProduct
