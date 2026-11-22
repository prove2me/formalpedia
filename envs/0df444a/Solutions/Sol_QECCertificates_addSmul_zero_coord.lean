-- Prove2me | solution 1 for QECCertificates.addSmul_zero_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:55.709404+00:00
-- url     : https://prove2.me/submissions/f4d1f538-2070-4be9-a799-0b906a9fec97

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_addSmul_apply
attribute [local simp] QECCertificates.addSmul_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v r : Vec n) (i : Fin n) (hr : r i = 1) :
    addSmul v r (v i) i = 0 := by
  rw [addSmul_apply, hr, mul_one]
  exact CharTwo.add_self_eq_zero (v i)
end QECCertificates
