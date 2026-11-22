-- Prove2me | solution 1 for QECCertificates.leadIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:04.447814+00:00
-- url     : https://prove2.me/submissions/5621139c-f845-4211-9af3-b2e6cc311500

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_leadIdx_spec
public import Theorems.Thm_QECCertificates_eq_one_of_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v : Vec n) (h : v ≠ 0) : v (leadIdx v h) = 1 :=
  eq_one_of_ne_zero (leadIdx_spec v h)
end QECCertificates
