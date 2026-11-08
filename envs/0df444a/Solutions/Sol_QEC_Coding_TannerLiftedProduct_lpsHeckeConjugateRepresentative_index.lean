-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateRepresentative_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:05:06.030201+00:00
-- url     : https://prove2.me/submissions/e007968b-1b4f-4310-97d8-5d4d398fdd11

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateCosetEquiv_mk


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp (lpsHeckeConjugateRepresentative N p hNp i:SL(2,ℤ))⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem
        (lpsHeckeConjugateRepresentative N p hNp i).property)
        (some ⟨0,(Fact.out:p.Prime).pos⟩)=i := by
  rw [←lpsHeckeConjugateCosetEquiv_mk]
  unfold lpsHeckeConjugateRepresentative
  have ho : (QuotientGroup.mk (Quotient.out ((lpsHeckeConjugateCosetEquiv N p hNp).symm i)) :
      CongruenceSubgroup.Gamma0 N ⧸ (lpsHeckeConjugateIntersection N p).subgroupOf (CongruenceSubgroup.Gamma0 N)) =
        (lpsHeckeConjugateCosetEquiv N p hNp).symm i := Quotient.out_eq' _
  exact (congrArg (lpsHeckeConjugateCosetEquiv N p hNp) ho).trans (Equiv.apply_symm_apply _ _)
end QEC.Coding.TannerLiftedProduct
