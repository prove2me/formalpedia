-- Prove2me | solution 1 for QECCertificates.LRAT.dotS_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:42:07.145554+00:00
-- url     : https://prove2.me/submissions/64ff77aa-397d-432c-bdec-577bdd16c382

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (j : Nat) (s : List Nat) :
    dotS σ (j :: s) = (σ j ^^ dotS σ s) := rfl
end QECCertificates.LRAT
