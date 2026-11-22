-- Prove2me | solution 1 for QECCertificates.PauliExpr.commutes_iff_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:25.462201+00:00
-- url     : https://prove2.me/submissions/da0a6fed-30f3-4a67-b42d-ec9a75831196

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
public import Theorems.Thm_QECCertificates_commutesWord_iff_symplectic

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
open QECCertificates.PauliExpr
namespace QECCertificates.PauliExpr
theorem _root_.solution (a b : PauliExpr n) :
    commutes a b ↔ (toSymp a).1 ⬝ᵥ (toSymp b).2 + (toSymp b).1 ⬝ᵥ (toSymp a).2 = 0 :=
  commutesWord_iff_symplectic (eval a) (eval b)
end QECCertificates.PauliExpr
