-- Prove2me | solution 1 for QECCertificates.sympWord_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:59.59082+00:00
-- url     : https://prove2.me/submissions/29a9867e-2f08-4d60-9b3b-886668016342

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (w : PauliWord n) : (sympWord w).1 = fun i => (Pauli.symp (w i)).1 := rfl
end QECCertificates
