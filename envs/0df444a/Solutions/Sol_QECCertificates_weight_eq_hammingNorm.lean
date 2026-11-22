-- Prove2me | solution 1 for QECCertificates.weight_eq_hammingNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:47:37.291869+00:00
-- url     : https://prove2.me/submissions/b0cc7869-de95-4d1a-a7b6-8474be349468

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.mem_support

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v : Vec n) : (support v).card = hammingNorm v := by
  simp [support, hammingNorm]
end QECCertificates
