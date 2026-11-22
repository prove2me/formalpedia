-- Prove2me | solution 1 for QECCertificates.rowReduce_mem_iff_of_spanL_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:51.777811+00:00
-- url     : https://prove2.me/submissions/1238f1f7-035f-4554-93a5-65979d311bdf

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Theorems.Thm_QECCertificates_pivRow_mem_iff_of_spanL_eq
public import Theorems.Thm_QECCertificates_isEchelon_rowReduce
public import Theorems.Thm_QECCertificates_spanL_rowReduce


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {L₁ L₂ : List (Vec n)} (h : spanL L₁ = spanL L₂)
    (x : PivRow n) : x ∈ rowReduce L₁ ↔ x ∈ rowReduce L₂ :=
  pivRow_mem_iff_of_spanL_eq (isEchelon_rowReduce L₁) (isEchelon_rowReduce L₂)
    (by rw [spanL_rowReduce, spanL_rowReduce, h]) x
end QECCertificates
