-- Prove2me | solution 1 for QECCertificates.Pauli.anti_eq_symp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:56.991799+00:00
-- url     : https://prove2.me/submissions/21aaee68-d3f8-4457-8a41-f2a301b8ea78

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
theorem _root_.solution (p q : Pauli) :
    anti p q = (symp p).1 * (symp q).2 + (symp q).1 * (symp p).2 := by
  fin_cases p <;> fin_cases q <;> decide
end QECCertificates.Pauli
