-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveHeckeConjugateCosetEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:05:03.975212+00:00
-- url     : https://prove2.me/submissions/bbfac34a-d1ed-4cc7-82fd-7a45ed746e02

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveKernel_le_HeckeConjugate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveRelativeCosetEquiv_mk


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsEffectiveHeckeConjugateCosetEquiv N p hNp
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ)) =
      lpsHeckeConjugateCosetEquiv N p hNp (QuotientGroup.mk γ) := by
  change lpsHeckeConjugateCosetEquiv N p hNp
    ((lpsEffectiveRelativeCosetEquiv N (lpsHeckeConjugateIntersection N p)
      (lpsEffectiveKernel_le_HeckeConjugate N p)).symm _) = _
  have hm := lpsEffectiveRelativeCosetEquiv_mk N (lpsHeckeConjugateIntersection N p) (lpsEffectiveKernel_le_HeckeConjugate N p) γ
  have hi := congrArg (lpsEffectiveRelativeCosetEquiv N (lpsHeckeConjugateIntersection N p) (lpsEffectiveKernel_le_HeckeConjugate N p)).symm hm
  have hi' : (lpsEffectiveRelativeCosetEquiv N (lpsHeckeConjugateIntersection N p) (lpsEffectiveKernel_le_HeckeConjugate N p)).symm
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ))=QuotientGroup.mk γ :=
    hi.symm.trans (Equiv.symm_apply_apply _ _)
  exact congrArg (lpsHeckeConjugateCosetEquiv N p hNp) hi'
end QEC.Coding.TannerLiftedProduct
