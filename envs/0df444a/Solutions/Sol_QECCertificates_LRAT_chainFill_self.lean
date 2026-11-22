-- Prove2me | solution 1 for QECCertificates.LRAT.chainFill_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:20.256238+00:00
-- url     : https://prove2.me/submissions/7b85cd7f-e0c0-4eab-b334-a317dff00969

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainFill_cons

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c : Nat) :
    chainFill σ (x :: rest) acc c c = (acc ^^ σ x) := by
  rw [chainFill_cons, if_pos rfl]
end QECCertificates.LRAT
