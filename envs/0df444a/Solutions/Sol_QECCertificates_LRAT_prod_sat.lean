-- Prove2me | solution 1 for QECCertificates.LRAT.prod_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:05.944806+00:00
-- url     : https://prove2.me/submissions/a15435b1-9312-42ac-935d-8f7928c5c989

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_sat_two
public import Theorems.Thm_QECCertificates_LRAT_sat_three
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {a x w : Nat}
    (h1 : SatClause σ [(a, false), (x, true)])
    (h2 : SatClause σ [(a, false), (w, true)])
    (h3 : SatClause σ [(a, true), (x, false), (w, false)]) :
    σ a = (σ x && σ w) := by
  have k1 : σ a = false ∨ σ x = true := sat_two h1
  have k2 : σ a = false ∨ σ w = true := sat_two h2
  have k3 : σ a = true ∨ σ x = false ∨ σ w = false := sat_three h3
  by_cases ha : σ a = true
  · have hx : σ x = true := by
      rcases k1 with h | h
      · exact absurd h (by simp [ha])
      · exact h
    have hw : σ w = true := by
      rcases k2 with h | h
      · exact absurd h (by simp [ha])
      · exact h
    simp [ha, hx, hw]
  · have ha' : σ a = false := by
      cases hh : σ a with
      | false => rfl
      | true => exact absurd hh ha
    rcases k3 with h | h | h
    · exact absurd (ha' ▸ h) (by simp)
    · simp [ha', h]
    · simp [ha', h]
end QECCertificates.LRAT
