-- Prove2me | solution 1 for QECCertificates.LRAT.xorChain_vars_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:11.368849+00:00
-- url     : https://prove2.me/submissions/49ea781e-6421-40a3-a706-c64c908b5791

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_snd
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_vars_lt
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
theorem _root_.solution {xs : List Nat} {w : Bool} {c : Nat} (hne : xs ≠ [])
    (hlt : ∀ t ∈ xs, t < c) :
    ∀ C ∈ (xorChain xs w c).1, ∀ l ∈ C, l.1 < (xorChain xs w c).2 := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x₀ t =>
      have hx₀ : x₀ < c := hlt x₀ (List.mem_cons_self ..)
      have ht : ∀ s ∈ t, s < c := fun s hs => hlt s (List.mem_cons_of_mem _ hs)
      have h := xorChainAux_snd t w x₀ c
      simp only [xorChain, h]
      exact xorChainAux_vars_lt t w x₀ c hx₀ ht
end QECCertificates.LRAT
