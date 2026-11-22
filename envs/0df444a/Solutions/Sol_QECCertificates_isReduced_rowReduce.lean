-- Prove2me | solution 1 for QECCertificates.isReduced_rowReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:43.571046+00:00
-- url     : https://prove2.me/submissions/667606ef-0aa9-458c-9e79-cd907a9280a2

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_isReduced_nil
public import Theorems.Thm_QECCertificates_isReduced_rowReduceFrom

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) : IsReduced (rowReduce L) :=
  isReduced_rowReduceFrom isReduced_nil L
end QECCertificates
