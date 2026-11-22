-- Prove2me | solution 1 for QECCertificates.finrank_spanL_eq_length_rowReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:14.87333+00:00
-- url     : https://prove2.me/submissions/fef4f9ac-2818-496b-989c-5519f7108af7

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_nodupPiv_rowReduce
public import Theorems.Thm_QECCertificates_finrank_spanL_eq_length_of_isReduced
public import Theorems.Thm_QECCertificates_isReduced_rowReduce
public import Theorems.Thm_QECCertificates_spanL_rowReduce


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) :
    Module.finrank (ZMod 2) (spanL L) = (rowReduce L).length := by
  rw [← spanL_rowReduce L]
  exact finrank_spanL_eq_length_of_isReduced (isReduced_rowReduce L) (nodupPiv_rowReduce L)
end QECCertificates
