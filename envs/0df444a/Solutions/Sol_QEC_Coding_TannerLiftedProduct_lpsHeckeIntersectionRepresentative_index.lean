-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeIntersectionRepresentative_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:04:51.347561+00:00
-- url     : https://prove2.me/submissions/1b4a5757-ef6c-40d2-bb02-b947ac154f12

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRelativeCosetDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersectionCosetEquiv_mk


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [Fact p.Prime]
    (hNp : p.Coprime N) (i : Option (Fin p)) :
    lpsHeckeRightIndex N p hNp (lpsHeckeIntersectionRepresentative N p hNp i:SL(2,ℤ))⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem
        (lpsHeckeIntersectionRepresentative N p hNp i).property) none=i := by
  rw [←lpsHeckeIntersectionCosetEquiv_mk]
  unfold lpsHeckeIntersectionRepresentative
  have ho : (QuotientGroup.mk (Quotient.out ((lpsHeckeIntersectionCosetEquiv N p hNp).symm i)) :
      CongruenceSubgroup.Gamma0 N ⧸ (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N)) =
        (lpsHeckeIntersectionCosetEquiv N p hNp).symm i := Quotient.out_eq' _
  exact (congrArg (lpsHeckeIntersectionCosetEquiv N p hNp) ho).trans (Equiv.apply_symm_apply _ _)
end QEC.Coding.TannerLiftedProduct
