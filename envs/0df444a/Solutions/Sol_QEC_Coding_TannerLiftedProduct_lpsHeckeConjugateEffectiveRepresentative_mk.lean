-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateEffectiveRepresentative_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:06:30.4886+00:00
-- url     : https://prove2.me/submissions/e94da0eb-25c3-4aef-8af7-35ef9a09fa59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveHeckeConjugateCosetEquiv_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    (QuotientGroup.mk (lpsHeckeConjugateEffectiveRepresentative N p hNp i) :
      lpsEffectiveGamma0 N ⧸ (lpsEffectiveHeckeConjugateIntersection N p).subgroupOf (lpsEffectiveGamma0 N)) =
        (lpsEffectiveHeckeConjugateCosetEquiv N p hNp).symm i := by
  apply (lpsEffectiveHeckeConjugateCosetEquiv N p hNp).injective
  rw [Equiv.apply_symm_apply]
  unfold lpsHeckeConjugateEffectiveRepresentative
  rw [lpsEffectiveHeckeConjugateCosetEquiv_mk]
  unfold lpsHeckeConjugateRepresentative
  have ho : (QuotientGroup.mk (Quotient.out ((lpsHeckeConjugateCosetEquiv N p hNp).symm i)) :
      CongruenceSubgroup.Gamma0 N ⧸ (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N)) =
        (lpsHeckeConjugateCosetEquiv N p hNp).symm i := Quotient.out_eq' _
  exact (congrArg (lpsHeckeConjugateCosetEquiv N p hNp) ho).trans (Equiv.apply_symm_apply _ _)
end QEC.Coding.TannerLiftedProduct
