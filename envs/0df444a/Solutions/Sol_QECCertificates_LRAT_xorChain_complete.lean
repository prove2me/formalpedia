-- Prove2me | solution 1 for QECCertificates.LRAT.xorChain_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:25.308765+00:00
-- url     : https://prove2.me/submissions/e877593d-26aa-4eea-a436-d93c3eb01b84

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainAssign_of_lt
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_complete
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
theorem _root_.solution {xs : List Nat} {w : Bool} {c : Nat} {σ : Assign}
    (hne : xs ≠ []) (hlt : ∀ t ∈ xs, t < c) (h : dotS σ xs = w) :
    ∃ τ : Assign, (∀ t, t < c → τ t = σ t) ∧
      ∀ C ∈ (xorChain xs w c).1, SatClause τ C := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x₀ t =>
      have hx₀ : x₀ < c := hlt x₀ (List.mem_cons_self ..)
      have ht : ∀ s ∈ t, s < c := fun s hs => hlt s (List.mem_cons_of_mem _ hs)
      exact ⟨chainAssign σ t (σ x₀) c, fun _ hu => chainAssign_of_lt hu,
        fun C hC => by
          simp only [xorChain] at hC
          exact xorChainAux_complete t w x₀ c σ hx₀ ht h C hC⟩
end QECCertificates.LRAT
