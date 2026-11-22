-- Prove2me | solution 1 for QECCertificates.Pauli.symp_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:49.429006+00:00
-- url     : https://prove2.me/submissions/31531ba8-c8ba-4f31-ba0e-739f264977ee

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
open QECCertificates.Pauli
namespace QECCertificates.Pauli
theorem _root_.solution (p q : Pauli) : symp (mul p q) = symp p + symp q := by
  fin_cases p <;> fin_cases q <;> decide
end QECCertificates.Pauli
