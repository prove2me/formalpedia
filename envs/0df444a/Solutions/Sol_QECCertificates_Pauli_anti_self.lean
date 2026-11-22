-- Prove2me | solution 1 for QECCertificates.Pauli.anti_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:47:06.555331+00:00
-- url     : https://prove2.me/submissions/5755f71e-4784-439e-987a-a2fcae3a6c5f

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
theorem _root_.solution (p : Pauli) : anti p p = 0 := by cases p <;> rfl
end QECCertificates.Pauli
