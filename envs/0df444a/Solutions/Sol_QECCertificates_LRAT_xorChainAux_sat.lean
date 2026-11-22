-- Prove2me | solution 1 for QECCertificates.LRAT.xorChainAux_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:04.270488+00:00
-- url     : https://prove2.me/submissions/a2bb5e9c-fc6e-4add-b86d-d511704d50ec

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_xorStep_sat
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution : ∀ (rest : List Nat) (want : Bool) (cur c : Nat) (σ : Assign),
    (∀ C ∈ (xorChainAux rest want cur c).1, SatClause σ C) →
    dotS σ (cur :: rest) = want := by
  intro rest
  induction rest with
  | nil =>
      intro want cur c σ h
      have hc : SatClause σ [(cur, want)] := h _ (by simp [xorChainAux])
      obtain ⟨l, hl, hv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      obtain rfl : l = (cur, want) := hl
      simp only [dotS_cons, dotS_nil]
      rw [hv]
      cases want <;> rfl
  | cons x rest ih =>
      intro want cur c σ h
      have hstep : ∀ C ∈ xorStepClauses cur x c, SatClause σ C :=
        fun C hC => h C (List.mem_append_left _ hC)
      have htl : ∀ C ∈ (xorChainAux rest want c (c + 1)).1, SatClause σ C :=
        fun C hC => h C (List.mem_append_right _ hC)
      have hnxt : σ c = (σ cur ^^ σ x) := xorStep_sat hstep
      have hIH : dotS σ (c :: rest) = want := ih want c (c + 1) σ htl
      simp only [dotS_cons] at hIH ⊢
      rw [hnxt] at hIH
      rw [← hIH, Bool.xor_assoc]
end QECCertificates.LRAT
