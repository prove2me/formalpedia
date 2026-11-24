-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.exists_chain_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:21.783702+00:00
-- url     : https://prove2.me/submissions/ab2eda41-96f5-4b45-aed4-677d86db43f5

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_toFinset_chainOfFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_iterNext_mem
import Theorems.Thm_OrdinalStepUp_ErdosRado_iterNext_strictMono
attribute [local simp] OrdinalStepUp.ErdosRado.toFinset_chainOfFinset

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution {𝒜 : Set SetOrd} {j L : ℕ} (hA : IsIndec (otp 𝒜))
    (hjL : j + 1 ≤ L) (v : Fin (j + 1) → SetOrd) (hv : ∀ i, v i ∈ 𝒜)
    (hvmono : ∀ i i' : Fin (j + 1), i < i' → v i ≺w v i') :
    ∃ u : FinChain L, (∀ i, u i ∈ 𝒜) ∧
      ∀ i : Fin (j + 1), u ⟨i, lt_of_lt_of_le i.isLt hjL⟩ = v i := by
  set top : SetOrd := v (Fin.last j) with htop
  set F : ℕ → SetOrd :=
    fun k => if h : k < j + 1 then v ⟨k, h⟩ else iterNext 𝒜 top (k - j) with hF
  have hFlt {k} (h : k < j + 1) : F k = v ⟨k, h⟩ := dif_pos h
  have hFge : ∀ k : ℕ, j + 1 ≤ k → F k = iterNext 𝒜 top (k - j) :=
    fun k h => dif_neg (by omega)
  have hcmem : ∀ k, iterNext 𝒜 top k ∈ 𝒜 := iterNext_mem hA (hv _)
  -- everything in the head sits at or below `top`, hence below all the padding
  have hlift {y : SetOrd} (hy: y = top ∨ y ≺w top) {k : ℕ} :  y ≺w iterNext 𝒜 top (k + 1) := by
    have hstep : top ≺w iterNext 𝒜 top (k + 1) :=
      iterNext_strictMono hA (hv _) (Nat.succ_pos k)
    rcases hy with rfl | hy
    · exact hstep
    · exact _root_.trans hy hstep
  have hFmem k: F k ∈ 𝒜 := by
    rcases Nat.lt_or_ge k (j + 1) with h | h
    · rw [hFlt h]; exact hv _
    · rw [hFge k h]; exact hcmem _
  have hFmono p q (hpq : p < q) : F p ≺w F q := by
    rcases Nat.lt_or_ge p (j + 1) with hp | hp
    · rcases Nat.lt_or_ge q (j + 1) with hq | hq
      · rw [hFlt hp, hFlt hq]
        exact hvmono _ _ (by simpa [Fin.lt_def] using hpq)
      · rw [hFlt hp, hFge q hq, (by omega: q - j = (q - j - 1) + 1)]
        refine hlift ?_
        rcases eq_or_lt_of_le (Fin.le_last (⟨p, hp⟩ : Fin (j + 1))) with h | h
        · exact Or.inl (by rw [htop, ← h])
        · exact Or.inr (hvmono _ _ h)
    · rw [hFge p hp, hFge q (by omega)]
      exact iterNext_strictMono hA (hv _) (by omega)
  exact ⟨FinChain.mk (fun i => F i) (hFmono · ·), fun _ => hFmem _, fun i => hFlt i.isLt⟩
end OrdinalStepUp.ErdosRado
