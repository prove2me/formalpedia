-- Prove2me | solution 1 for QECCertificates.LRAT.chainFill_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:44.088803+00:00
-- url     : https://prove2.me/submissions/605c3729-a293-4dd9-bf19-c1338b8b2b61

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (acc : Bool) (c t : Nat) :
    chainFill σ [] acc c t = false := rfl
end QECCertificates.LRAT
