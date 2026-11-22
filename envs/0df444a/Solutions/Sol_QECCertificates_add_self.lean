-- Prove2me | solution 1 for QECCertificates.add_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:04.027805+00:00
-- url     : https://prove2.me/submissions/5a14c3d7-ab9b-4f4a-bf3c-a75d18d15b24

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v : Vec n) : v + v = 0 := by
  funext i; exact CharTwo.add_self_eq_zero (v i)
end QECCertificates
