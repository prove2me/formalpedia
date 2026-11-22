-- Prove2me | solution 1 for QECCertificates.LRAT.chainAssign_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:46.000813+00:00
-- url     : https://prove2.me/submissions/752f6803-fc76-4ea9-bf86-8343290e9668

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainFill_self
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
attribute [local simp] QECCertificates.LRAT.cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c : Nat) :
    chainAssign σ (x :: rest) acc c c = (acc ^^ σ x) := by
  simp only [chainAssign, Nat.lt_irrefl, ite_false]
  exact chainFill_self σ x rest acc c
end QECCertificates.LRAT
