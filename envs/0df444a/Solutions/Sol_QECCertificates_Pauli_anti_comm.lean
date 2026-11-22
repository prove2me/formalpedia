-- Prove2me | solution 1 for QECCertificates.Pauli.anti_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:54.252418+00:00
-- url     : https://prove2.me/submissions/9d1426e3-e32f-4514-91a1-301bb643ae49

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
theorem _root_.solution (p q : Pauli) : anti p q = anti q p := by fin_cases p <;> fin_cases q <;> decide
end QECCertificates.Pauli
