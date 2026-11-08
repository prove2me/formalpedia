-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionEffectiveRepresentative_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:06:43.604222+00:00
-- url     : https://prove2.me/submissions/40bd4531-8794-44d5-b7b2-99045ab121d5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveHeckeIntersectionCosetEquiv_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    (QuotientGroup.mk (lpsHeckeIntersectionEffectiveRepresentative N p hNp i) :
      lpsEffectiveGamma0 N ⧸ (lpsEffectiveGamma0 (N*p)).subgroupOf (lpsEffectiveGamma0 N)) =
        (lpsEffectiveHeckeIntersectionCosetEquiv N p hNp).symm i := by
  apply (lpsEffectiveHeckeIntersectionCosetEquiv N p hNp).injective
  rw [Equiv.apply_symm_apply]
  unfold lpsHeckeIntersectionEffectiveRepresentative
  rw [lpsEffectiveHeckeIntersectionCosetEquiv_mk]
  unfold lpsHeckeIntersectionRepresentative
  have ho : (QuotientGroup.mk (Quotient.out ((lpsHeckeIntersectionCosetEquiv N p hNp).symm i)) :
      CongruenceSubgroup.Gamma0 N ⧸ (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N)) =
        (lpsHeckeIntersectionCosetEquiv N p hNp).symm i := Quotient.out_eq' _
  exact (congrArg (lpsHeckeIntersectionCosetEquiv N p hNp) ho).trans (Equiv.apply_symm_apply _ _)
end QEC.Coding.TannerLiftedProduct
