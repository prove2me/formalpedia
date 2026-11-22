-- Prove2me | solution 1 for QECCertificates.LRAT.sat_three_of_imp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:40.106379+00:00
-- url     : https://prove2.me/submissions/de69d99b-9469-461d-94e9-00ca2d91e1d7

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
theorem _root_.solution {τ : Assign} {s a x : Nat} {bs ba bx : Bool}
    (hs : τ s = bs) (ha : τ a = ba) (hx : τ x = bx)
    (h : bs = true → ba = false → bx = true) :
    SatClause τ [(s, false), (a, true), (x, true)] := by
  cases bs with
  | false => exact ⟨(s, false), by simp, by rw [hs]⟩
  | true =>
      cases ba with
      | false => exact ⟨(x, true), by simp, by rw [hx]; exact h rfl rfl⟩
      | true => exact ⟨(a, true), by simp, by rw [ha]⟩
end QECCertificates.LRAT
