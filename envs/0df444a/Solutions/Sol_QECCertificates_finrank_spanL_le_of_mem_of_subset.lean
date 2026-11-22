-- Prove2me | solution 1 for QECCertificates.finrank_spanL_le_of_mem_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:40.558392+00:00
-- url     : https://prove2.me/submissions/7b040cb9-dd36-49fc-8eab-aebb2bee2743

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Theorems.Thm_QECCertificates_finrank_spanL_le_length

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {A L : List (Vec n)}
    (h : ∀ v ∈ L, v ∈ spanL A) :
    Module.finrank (ZMod 2) (spanL L) ≤ A.length := by
  have hle : spanL L ≤ spanL A := Submodule.span_le.mpr h
  exact le_trans (Submodule.finrank_mono hle) (finrank_spanL_le_length A)
end QECCertificates
