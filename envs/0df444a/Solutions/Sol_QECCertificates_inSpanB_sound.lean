-- Prove2me | solution 1 for QECCertificates.inSpanB_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:59.554148+00:00
-- url     : https://prove2.me/submissions/2e976b42-bfdf-4e0d-bc3a-57e540cfef57

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Theorems.Thm_QECCertificates_add_reduceAgainst_mem
public import Theorems.Thm_QECCertificates_spanL_rowReduce


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {L : List (Vec n)} {v : Vec n} (h : inSpanB L v = true) :
    v ∈ spanL L := by
  unfold inSpanB at h
  rw [decide_eq_true_eq] at h
  have hmem : v + reduceAgainst (rowReduce L) v ∈ spanL (rowList (rowReduce L)) :=
    add_reduceAgainst_mem (rowReduce L) v
  rw [h, add_zero] at hmem
  rwa [spanL_rowReduce] at hmem
end QECCertificates
