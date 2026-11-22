-- Prove2me | solution 1 for QECCertificates.LRAT.sat_two_of_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:16:35.323837+00:00
-- url     : https://prove2.me/submissions/22f1aa06-f350-4ebb-845d-bc16707fa035

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
theorem _root_.solution {τ : Assign} {p q : Nat} {bp bq : Bool}
    (hp : τ p = bp) (hq : τ q = bq) (h : bp = true → bq = true) :
    SatClause τ [(p, false), (q, true)] := by
  cases bp with
  | false => exact ⟨(p, false), by simp, by rw [hp]⟩
  | true => exact ⟨(q, true), by simp, by rw [hq]; exact h rfl⟩
end QECCertificates.LRAT
