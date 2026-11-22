-- Prove2me | solution 1 for QECCertificates.LRAT.atMostK_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:46.56816+00:00
-- url     : https://prove2.me/submissions/2803747d-09ab-4b13-aa79-1fa6697d51a2

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_atMostKAux_sat
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {σ : Assign} {s : Nat → Nat → Option Nat} {k : Nat}
    (hok : SlotOK s k) {xs : List Nat}
    (h : ∀ C ∈ atMostK s k xs, SatClause σ C) :
    cntS σ xs ≤ k := by
  have hinv0 : ∀ j, 1 ≤ j → j ≤ min ([] : List Nat).length (k + 1) →
      j ≤ cntS σ ([] : List Nat) → ∃ v, s ([] : List Nat).length j = some v ∧ σ v = true := by
    intro j hj1 hj2 _
    simp only [List.length_nil, Nat.min_eq_left (Nat.zero_le _), Nat.le_zero] at hj2
    omega
  have := atMostKAux_sat hok (pre := []) (suf := xs) hinv0 h
  simpa using this
end QECCertificates.LRAT
