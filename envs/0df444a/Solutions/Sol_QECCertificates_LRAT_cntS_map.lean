-- Prove2me | solution 1 for QECCertificates.LRAT.cntS_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:34.994883+00:00
-- url     : https://prove2.me/submissions/e454b11a-b7bb-4086-bdc1-561e7c8257d9

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
theorem _root_.solution (σ : Assign) (f : Nat → Nat) (l : List Nat) :
    cntS σ (l.map f) = cntS (fun t => σ (f t)) l := by
  simp only [cntS, List.filter_map, List.length_map, Function.comp_def]
end QECCertificates.LRAT
