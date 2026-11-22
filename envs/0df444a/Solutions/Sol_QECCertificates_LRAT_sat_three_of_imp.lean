-- Prove2me | solution 1 for QECCertificates.LRAT.sat_three_of_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:39.646131+00:00
-- url     : https://prove2.me/submissions/1284d4c1-d592-4f28-bfee-9c1135f422ec

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
theorem _root_.solution {τ : Assign} {a x s : Nat} {ba bx bs : Bool}
    (ha : τ a = ba) (hx : τ x = bx) (hs : τ s = bs)
    (h : ba = true → bx = true → bs = true) :
    SatClause τ [(a, false), (x, false), (s, true)] := by
  cases ba with
  | false => exact ⟨(a, false), by simp, by rw [ha]⟩
  | true =>
      cases bx with
      | false => exact ⟨(x, false), by simp, by rw [hx]⟩
      | true => exact ⟨(s, true), by simp, by rw [hs]; exact h rfl rfl⟩
end QECCertificates.LRAT
