-- Prove2me | solution 1 for QECCertificates.PauliExpr.eval_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:15.570259+00:00
-- url     : https://prove2.me/submissions/9b360069-8996-4918-9c54-f740099f2efc

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
theorem _root_.solution (a b : PauliExpr n) :
    eval (.mul a b) = fun i => Pauli.mul (eval a i) (eval b i) := rfl
end QECCertificates.PauliExpr
