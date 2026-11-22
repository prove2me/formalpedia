-- Prove2me | solution 1 for QECCertificates.LRAT.chainFill_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:48.651961+00:00
-- url     : https://prove2.me/submissions/a05916c4-0267-4b24-82ef-31500f55ad5e

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c t : Nat) :
    chainFill σ (x :: rest) acc c t =
      (if t = c then (acc ^^ σ x) else chainFill σ rest (acc ^^ σ x) (c + 1) t) := rfl
end QECCertificates.LRAT
