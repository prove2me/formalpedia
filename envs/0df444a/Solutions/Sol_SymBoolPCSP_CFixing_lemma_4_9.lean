-- Prove2me | solution 1 for SymBoolPCSP.CFixing.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-05T20:18:16.792164+00:00
-- url     : https://prove2.me/submissions/5b7e14bf-2748-46ab-a153-46f7826bdd52

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_9_bounded_explicit

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

theorem lemma_4_9 (n : ℕ) (hn : 0 < n) :
    (Odd n → ∃ A : ℕ, ∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
      (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
      (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
      A ∈ S₀ ∧ A ∈ S₁) ∧
    (Even n → ∃ d : ℕ, ∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
      (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
      (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
      (∀ m : ℕ, d ≤ m → Even m → m ∈ S₀) ∧ (∀ m : ℕ, d ≤ m → Odd m → m ∈ S₁)) := by
  refine ⟨fun hodd => ⟨(if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)), fun S₀ S₁ h0 h1 hs0 hs1 => ?_⟩,
    fun heven => ⟨(if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)), fun S₀ S₁ h0 h1 hs0 hs1 => ⟨fun M hM hMe => ?_, fun M hM hMo => ?_⟩⟩⟩
  · exact (lemma_4_9_bounded_explicit n _ hn S₀ S₁ h0 h1 (fun b hb _ => hs0 b hb)
      (fun a ha b hb _ => hs1 a ha b hb)).1 hodd le_rfl
  · exact ((lemma_4_9_bounded_explicit n M hn S₀ S₁ h0 h1 (fun b hb _ => hs0 b hb)
      (fun a ha b hb _ => hs1 a ha b hb)).2 heven M hM le_rfl).1 hMe
  · exact ((lemma_4_9_bounded_explicit n M hn S₀ S₁ h0 h1 (fun b hb _ => hs0 b hb)
      (fun a ha b hb _ => hs1 a ha b hb)).2 heven M hM le_rfl).2 hMo

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution (n : ℕ) (hn : 0 < n) :
    (Odd n → ∃ A : ℕ, ∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
      (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
      (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
      A ∈ S₀ ∧ A ∈ S₁) ∧
    (Even n → ∃ d : ℕ, ∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
      (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
      (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
      (∀ m : ℕ, d ≤ m → Even m → m ∈ S₀) ∧ (∀ m : ℕ, d ≤ m → Odd m → m ∈ S₁)) :=
  SymBoolPCSP.CFixing.lemma_4_9 n hn
