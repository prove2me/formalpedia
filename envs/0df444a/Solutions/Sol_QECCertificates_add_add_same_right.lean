-- Prove2me | solution 1 for QECCertificates.add_add_same_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:02.127337+00:00
-- url     : https://prove2.me/submissions/e678f035-6154-431f-be42-bd8a1cdd4d5f

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_add_add_same_left

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v w : Vec n) : v + (w + v) = w := by
  rw [add_comm w v, add_add_same_left]
end QECCertificates
