-- Prove2me | solution 1 for QECCertificates.LRAT.chainAssign_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:49.026807+00:00
-- url     : https://prove2.me/submissions/0f7cf3a2-7df9-4b5c-ae08-f20902eaba9f

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainFill_succ
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
theorem _root_.solution (σ : Assign) (x : Nat) (rest : List Nat) (acc : Bool) (c t : Nat)
    (h : c < t) :
    chainAssign σ (x :: rest) acc c t = chainAssign σ rest (acc ^^ σ x) (c + 1) t := by
  have h1 : ¬ t < c := by omega
  have h2 : ¬ t = c := by omega
  have h3 : ¬ t < c + 1 := by omega
  simp only [chainAssign, h1, h3, ite_false]
  rw [chainFill_succ σ x rest acc c t h2]
end QECCertificates.LRAT
