-- Prove2me | solution 1 for QECCertificates.inSpanB_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:10.998159+00:00
-- url     : https://prove2.me/submissions/28759819-4f8c-44d8-b486-21a402819dad

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Theorems.Thm_QECCertificates_reduceAgainst_eq_zero_of_mem_spanL
public import Theorems.Thm_QECCertificates_isReduced_rowReduce
public import Theorems.Thm_QECCertificates_spanL_rowReduce


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {L : List (Vec n)} {v : Vec n} (hv : v ∈ spanL L) :
    inSpanB L v = true := by
  unfold inSpanB
  rw [decide_eq_true_eq]
  exact reduceAgainst_eq_zero_of_mem_spanL (isReduced_rowReduce L) (by rwa [spanL_rowReduce])
end QECCertificates
