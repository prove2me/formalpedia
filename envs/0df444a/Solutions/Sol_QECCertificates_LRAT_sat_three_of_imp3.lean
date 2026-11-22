-- Prove2me | solution 1 for QECCertificates.LRAT.sat_three_of_imp3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:43.10617+00:00
-- url     : https://prove2.me/submissions/a19fc9a2-9cc8-400c-896a-ccdf676e2899

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
theorem _root_.solution {τ : Assign} {s a b : Nat} {bs ba bb : Bool}
    (hs : τ s = bs) (ha : τ a = ba) (hb : τ b = bb)
    (h : bs = true → ba = false → bb = true) :
    SatClause τ [(s, false), (a, true), (b, true)] := by
  cases bs with
  | false => exact ⟨(s, false), by simp, by rw [hs]⟩
  | true =>
      cases ba with
      | false => exact ⟨(b, true), by simp, by rw [hb]; exact h rfl rfl⟩
      | true => exact ⟨(a, true), by simp, by rw [ha]⟩
end QECCertificates.LRAT
