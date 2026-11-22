-- Prove2me | solution 1 for QECCertificates.nodupPiv_rowReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:38.622159+00:00
-- url     : https://prove2.me/submissions/1814e454-c047-4fbc-ad0d-9e94e4698e62

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_nodupPiv_nil
public import Theorems.Thm_QECCertificates_nodupPiv_rowReduceFrom
public import Theorems.Thm_QECCertificates_isReduced_nil


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) : NodupPiv (rowReduce L) :=
  nodupPiv_rowReduceFrom [] L isReduced_nil nodupPiv_nil
end QECCertificates
