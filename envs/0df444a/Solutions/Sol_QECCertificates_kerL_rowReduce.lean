-- Prove2me | solution 1 for QECCertificates.kerL_rowReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:31.545249+00:00
-- url     : https://prove2.me/submissions/c21eccf0-bb78-4854-bb28-c89decd8ea00

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_kerL_eq_of_spanL_eq
public import Theorems.Thm_QECCertificates_kerVec_mem_kerL
public import Theorems.Thm_QECCertificates_mem_kerBasis
public import Theorems.Thm_QECCertificates_kerL_le_spanL_kerBasis
public import Theorems.Thm_QECCertificates_isReduced_rowReduce
public import Theorems.Thm_QECCertificates_spanL_rowReduce


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) :
    kerL L = spanL (kerBasis (rowReduce L)) := by
  rw [← kerL_eq_of_spanL_eq (spanL_rowReduce L)]
  refine le_antisymm (kerL_le_spanL_kerBasis (isReduced_rowReduce L)) ?_
  refine Submodule.span_le.2 fun x hx => ?_
  have hx' : x ∈ kerBasis (rowReduce L) := hx
  rw [mem_kerBasis] at hx'
  obtain ⟨j, -, rfl⟩ := hx'
  exact kerVec_mem_kerL (isReduced_rowReduce L) j
end QECCertificates
