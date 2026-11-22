-- Prove2me | solution 1 for QECCertificates.vee_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:44:15.902033+00:00
-- url     : https://prove2.me/submissions/eab705a7-783d-4239-b7fb-6824fe4feb04

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}
namespace QECCertificates
theorem _root_.solution (u : Fin a → Vec p) (C : VMat a s) (i : Fin p) (j : Fin s) :
    vee u C (i, j) = ∑ k, C (k, j) * u k i := rfl
end QECCertificates
