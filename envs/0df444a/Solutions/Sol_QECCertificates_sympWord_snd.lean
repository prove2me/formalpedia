-- Prove2me | solution 1 for QECCertificates.sympWord_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:01.550541+00:00
-- url     : https://prove2.me/submissions/8952d4b2-f811-464f-ab7a-881808a1624a

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
theorem _root_.solution (w : PauliWord n) : (sympWord w).2 = fun i => (Pauli.symp (w i)).2 := rfl
end QECCertificates
