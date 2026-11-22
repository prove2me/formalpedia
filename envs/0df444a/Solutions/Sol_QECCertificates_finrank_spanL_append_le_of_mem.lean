-- Prove2me | solution 1 for QECCertificates.finrank_spanL_append_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:18.062156+00:00
-- url     : https://prove2.me/submissions/2d1aee51-79c5-40be-9cde-765101a510dd

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_finrank_spanL_le_of_mem_of_subset
public import Theorems.Thm_QECCertificates_subset_spanL


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (A B : List (Vec n))
    (h : ∀ v ∈ B, v ∈ spanL A) :
    Module.finrank (ZMod 2) (spanL (A ++ B)) ≤ A.length := by
  have hA : ∀ v ∈ A ++ B, v ∈ spanL A := by
    intro v hv
    rw [List.mem_append] at hv
    rcases hv with hv | hv
    · exact subset_spanL hv
    · exact h v hv
  exact finrank_spanL_le_of_mem_of_subset hA
end QECCertificates
