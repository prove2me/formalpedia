-- Prove2me | solution 1 for QECCertificates.PauliExpr.eval_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:10.418933+00:00
-- url     : https://prove2.me/submissions/3352f1f3-df03-44eb-8a00-baabfe671db9

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
open QECCertificates.PauliExpr
namespace QECCertificates.PauliExpr
theorem _root_.solution : eval (.one : PauliExpr n) = fun _ => Pauli.I := rfl
end QECCertificates.PauliExpr
