-- Prove2me | solution 1 for QECCertificates.LRAT.cntS_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:51.436578+00:00
-- url     : https://prove2.me/submissions/5c6c014f-10b4-4ec9-a5c0-9d5f6cc27a80

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (σ : Assign) (l₁ l₂ : List Nat) :
    cntS σ (l₁ ++ l₂) = cntS σ l₁ + cntS σ l₂ := by
  simp [cntS, List.filter_append]
end QECCertificates.LRAT
