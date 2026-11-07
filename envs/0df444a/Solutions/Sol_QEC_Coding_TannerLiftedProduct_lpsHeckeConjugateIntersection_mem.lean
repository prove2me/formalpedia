-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:13:14.731889+00:00
-- url     : https://prove2.me/submissions/c2ca1f6a-1163-4313-a935-3ebf3f6ff096

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) (γ : SL(2,ℤ)) :
    γ ∈ lpsHeckeConjugateIntersection N p ↔
      γ ∈ CongruenceSubgroup.Gamma0 N ∧ (p:ℤ) ∣ γ 0 1 := by
  change (γ ∈ CongruenceSubgroup.Gamma0 N ∧ (γ 0 1:ZMod p)=0) ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
end QEC.Coding.TannerLiftedProduct
