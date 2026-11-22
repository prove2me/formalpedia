-- Prove2me | solution 1 for QECCertificates.exists_light_mem_kerL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:18.271094+00:00
-- url     : https://prove2.me/submissions/b1751475-99b4-4a1b-b796-8b55c7e88f3b

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_mem_pivCols
public import Theorems.Thm_QECCertificates_kerVec_ne_zero
public import Theorems.Thm_QECCertificates_hammingNorm_kerVec_le
public import Theorems.Thm_QECCertificates_mem_kerBasis
public import Theorems.Thm_QECCertificates_kerL_rowReduce
public import Theorems.Thm_QECCertificates_subset_spanL


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) {j : Fin n}
    (hj : IsFreeCol (rowReduce L) j) :
    ∃ v ∈ kerL L, v ≠ 0 ∧ hammingNorm v ≤ (rowReduce L).length + 1 := by
  refine ⟨kerVec (rowReduce L) j, ?_, kerVec_ne_zero hj, hammingNorm_kerVec_le _ _⟩
  rw [kerL_rowReduce]
  refine subset_spanL (mem_kerBasis.mpr ⟨j, fun hmem => ?_, rfl⟩)
  obtain ⟨ri, hri, hcon⟩ := mem_pivCols.mp hmem
  exact hj ri hri hcon
end QECCertificates
