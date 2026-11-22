-- Prove2me | solution 1 for QECCertificates.LRAT.slotClauses_eq_some_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:44.945888+00:00
-- url     : https://prove2.me/submissions/0d4c4014-b6ca-4845-b6fb-c6a86941fda2

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
theorem _root_.solution {s : Nat → Nat → Option Nat} {i j x a b si : Nat}
    (ha : s (i - 1) j = some a) (hb : s (i - 1) (j - 1) = some b) (hs : s i j = some si) :
    slotClauses s i j x =
      [[(a, false), (si, true)], [(b, false), (x, false), (si, true)],
       [(si, false), (a, true), (x, true)], [(si, false), (a, true), (b, true)]] := by
  simp only [slotClauses, ha, hb, hs]
end QECCertificates.LRAT
