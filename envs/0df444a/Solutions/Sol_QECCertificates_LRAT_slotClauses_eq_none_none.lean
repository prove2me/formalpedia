-- Prove2me | solution 1 for QECCertificates.LRAT.slotClauses_eq_none_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:53.977936+00:00
-- url     : https://prove2.me/submissions/15ae0ce1-7e9f-4219-a16d-7220995f71ca

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
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
theorem _root_.solution {s : Nat → Nat → Option Nat} {i j x si : Nat}
    (ha : s (i - 1) j = none) (hb : s (i - 1) (j - 1) = none) (hs : s i j = some si) :
    slotClauses s i j x = [[(x, false), (si, true)], [(si, false), (x, true)]] := by
  simp only [slotClauses, ha, hb, hs]
end QECCertificates.LRAT
