-- Prove2me | solution 1 for SymBoolPCSP.CFixing.remark_4_9
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-05T20:18:18.287577+00:00
-- url     : https://prove2.me/submissions/10171fc8-e216-4847-a16a-92589a19a03a

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_9_bounded_explicit
import Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_9

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

theorem remark_4_9 (n : ℕ) (hn : 0 < n) :
    (Odd n → ∃ A : ℕ,
      (∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
        A ∈ S₀ ∧ A ∈ S₁) ∧
      (∀ N : ℕ, 0 < N → A ≤ N → ∀ S₀ S₁ : Set ℕ, S₀ ⊆ Set.Iic N → S₁ ⊆ Set.Iic N →
        0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
          a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) →
        A ∈ S₀ ∧ A ∈ S₁)) ∧
    (Even n → ∃ d : ℕ,
      (∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
        (∀ m : ℕ, d ≤ m → Even m → m ∈ S₀) ∧ (∀ m : ℕ, d ≤ m → Odd m → m ∈ S₁)) ∧
      (∀ N : ℕ, 0 < N → d ≤ N → ∀ S₀ S₁ : Set ℕ, S₀ ⊆ Set.Iic N → S₁ ⊆ Set.Iic N →
        0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
          a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) →
        (∀ m : ℕ, d ≤ m → m ≤ N → Even m → m ∈ S₀) ∧
        (∀ m : ℕ, d ≤ m → m ≤ N → Odd m → m ∈ S₁))) := by
  have key := fun N S₀ S₁ h0 h1 hs0 hs1 =>
    lemma_4_9_bounded_explicit n N hn S₀ S₁ h0 h1 hs0 hs1
  obtain ⟨hlo, hle⟩ := lemma_4_9 n hn
  refine ⟨fun hodd => ⟨(if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)), ?_, ?_⟩, fun heven => ⟨(if n = 1 then 0 else 1 + (2 * n - 2) * (3 * n - 4)), ?_, ?_⟩⟩
  · intro S₀ S₁ h0 h1 hs0 hs1
    exact (key _ S₀ S₁ h0 h1 (fun b hb _ => hs0 b hb) (fun a ha b hb _ => hs1 a ha b hb)).1 hodd le_rfl
  · intro N _ hcN S₀ S₁ _ _ h0 h1 hs0 hs1
    exact (key N S₀ S₁ h0 h1 hs0 hs1).1 hodd hcN
  · intro S₀ S₁ h0 h1 hs0 hs1
    exact ⟨fun M hM hMe => ((key M S₀ S₁ h0 h1 (fun b hb _ => hs0 b hb)
        (fun a ha b hb _ => hs1 a ha b hb)).2 heven M hM le_rfl).1 hMe,
      fun M hM hMo => ((key M S₀ S₁ h0 h1 (fun b hb _ => hs0 b hb)
        (fun a ha b hb _ => hs1 a ha b hb)).2 heven M hM le_rfl).2 hMo⟩
  · intro N _ _ S₀ S₁ _ _ h0 h1 hs0 hs1
    exact ⟨fun M hM hMN hMe => ((key N S₀ S₁ h0 h1 hs0 hs1).2 heven M hM hMN).1 hMe,
      fun M hM hMN hMo => ((key N S₀ S₁ h0 h1 hs0 hs1).2 heven M hM hMN).2 hMo⟩

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution (n : ℕ) (hn : 0 < n) :
    (Odd n → ∃ A : ℕ,
      (∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
        A ∈ S₀ ∧ A ∈ S₁) ∧
      (∀ N : ℕ, 0 < N → A ≤ N → ∀ S₀ S₁ : Set ℕ, S₀ ⊆ Set.Iic N → S₁ ⊆ Set.Iic N →
        0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
          a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) →
        A ∈ S₀ ∧ A ∈ S₁)) ∧
    (Even n → ∃ d : ℕ,
      (∀ S₀ S₁ : Set ℕ, 0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) → a + ∑ i, b i ∈ S₁) →
        (∀ m : ℕ, d ≤ m → Even m → m ∈ S₀) ∧ (∀ m : ℕ, d ≤ m → Odd m → m ∈ S₁)) ∧
      (∀ N : ℕ, 0 < N → d ≤ N → ∀ S₀ S₁ : Set ℕ, S₀ ⊆ Set.Iic N → S₁ ⊆ Set.Iic N →
        0 ∈ S₀ → 1 ∈ S₁ →
        (∀ b : Fin n → ℕ, (∀ i, b i ∈ S₁) → ∑ i, b i ≤ N → ∑ i, b i ∈ S₀) →
        (∀ a ∈ S₀, ∀ b : Fin (n - 1) → ℕ, (∀ i, b i ∈ S₁) →
          a + ∑ i, b i ≤ N → a + ∑ i, b i ∈ S₁) →
        (∀ m : ℕ, d ≤ m → m ≤ N → Even m → m ∈ S₀) ∧
        (∀ m : ℕ, d ≤ m → m ≤ N → Odd m → m ∈ S₁))) :=
  SymBoolPCSP.CFixing.remark_4_9 n hn
