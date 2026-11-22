-- Prove2me | solution 1 for QECCertificates.Pauli.mul_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:09.437563+00:00
-- url     : https://prove2.me/submissions/65518de8-8e4b-4a3c-8481-5ef5f99bf128

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
theorem _root_.solution (p q r : Pauli) : mul (mul p q) r = mul p (mul q r) := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> rfl
end QECCertificates.Pauli
