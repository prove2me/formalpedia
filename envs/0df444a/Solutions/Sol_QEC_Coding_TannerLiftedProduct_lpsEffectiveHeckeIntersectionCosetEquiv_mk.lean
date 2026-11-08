-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveHeckeIntersectionCosetEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:04:48.904195+00:00
-- url     : https://prove2.me/submissions/3fd043e0-36ae-4403-9264-dea46e139e82

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveRelativeCosetEquiv_mk


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (γ : CongruenceSubgroup.Gamma0 N) :
    lpsEffectiveHeckeIntersectionCosetEquiv N p hNp
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ)) =
      lpsHeckeIntersectionCosetEquiv N p hNp (QuotientGroup.mk γ) := by
  change lpsHeckeIntersectionCosetEquiv N p hNp
    ((lpsEffectiveRelativeCosetEquiv N (CongruenceSubgroup.Gamma0 (N*p))
      (lpsEffectiveKernel_le_Gamma0 (N*p))).symm _) = _
  have hm := lpsEffectiveRelativeCosetEquiv_mk N (CongruenceSubgroup.Gamma0 (N*p)) (lpsEffectiveKernel_le_Gamma0 (N*p)) γ
  have hi := congrArg (lpsEffectiveRelativeCosetEquiv N (CongruenceSubgroup.Gamma0 (N*p)) (lpsEffectiveKernel_le_Gamma0 (N*p))).symm hm
  have hi' : (lpsEffectiveRelativeCosetEquiv N (CongruenceSubgroup.Gamma0 (N*p)) (lpsEffectiveKernel_le_Gamma0 (N*p))).symm
      (QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ))=QuotientGroup.mk γ :=
    hi.symm.trans (Equiv.symm_apply_apply _ _)
  exact congrArg (lpsHeckeIntersectionCosetEquiv N p hNp) hi'
end QEC.Coding.TannerLiftedProduct
