-- Prove2me | solution 1 for QECCertificates.exists_light_mem_kerL_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:30.508934+00:00
-- url     : https://prove2.me/submissions/592ba759-3787-4b4e-96ec-d3758e313181

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_mem_pivCols
public import Theorems.Thm_QECCertificates_kerVec_apply_free
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
    kerVec (rowReduce L) j ∈ kerL L
      ∧ hammingNorm (kerVec (rowReduce L) j) ≤ (rowReduce L).length + 1
      ∧ kerVec (rowReduce L) j j = 1 := by
  refine ⟨?_, hammingNorm_kerVec_le _ _, ?_⟩
  · rw [kerL_rowReduce]
    refine subset_spanL (mem_kerBasis.mpr ⟨j, fun hmem => ?_, rfl⟩)
    obtain ⟨ri, hri, hcon⟩ := mem_pivCols.mp hmem
    exact hj ri hri hcon
  · rw [kerVec_apply_free hj, if_pos rfl]
end QECCertificates
