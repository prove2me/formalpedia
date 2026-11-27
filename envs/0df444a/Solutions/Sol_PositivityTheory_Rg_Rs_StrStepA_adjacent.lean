-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.StrStepA.adjacent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:19:35.213064+00:00
-- url     : https://prove2.me/submissions/5bc5f23a-e28e-4213-ad11-834edcafa2a3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_PStringStepA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.StrStepA
namespace PositivityTheory.Rg.Rs.StrStepA
theorem _root_.solution (c₁ c₂ : ℝ) (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (S : Set ℝ)
    (hS : ∀ x, x ∈ S ↔ (∃ i : ℕ, i < d₁ ∧ x = c₁ + ((d₁ : ℝ) - 1) / 2 - i) ∨
      ∃ j : ℕ, j < d₂ ∧ x = c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hdisj : ∀ i j : ℕ, i < d₁ → j < d₂ → c₁ + ((d₁ : ℝ) - 1) / 2 - i ≠ c₂ + ((d₂ : ℝ) - 1) / 2 - j)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n)
    (hneg : ∀ x ∈ S, -x ∈ S) (hP : ∀ u ∈ S, 1 ≤ u → u - 1 ∈ S) (hc : c₁ < c₂) :
    c₂ - c₁ = ((d₁ : ℝ) + d₂) / 2 := by
  set e₁ : ℝ := ((d₁ : ℝ) - 1) / 2 with he₁
  set e₂ : ℝ := ((d₂ : ℝ) - 1) / 2 with he₂
  have hd₁' : (1 : ℝ) ≤ d₁ := by exact_mod_cast hd₁
  have hd₂' : (1 : ℝ) ≤ d₂ := by exact_mod_cast hd₂
  have he₁0 : 0 ≤ e₁ := by rw [he₁]; linarith
  have he₂0 : 0 ≤ e₂ := by rw [he₂]; linarith
  have hcast₁ : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1 := by rw [Nat.cast_sub hd₁]; simp
  have hcast₂ : ((d₂ - 1 : ℕ) : ℝ) = d₂ - 1 := by rw [Nat.cast_sub hd₂]; simp
  set B : ℝ := c₁ + e₁ with hBdef
  set C : ℝ := c₂ + e₂ - ((d₂ : ℝ) - 1) with hCdef
  have hB : B ∈ S := (hS _).2 (Or.inl ⟨0, hd₁, by simp [hBdef]⟩)
  have hC : C ∈ S := (hS _).2 (Or.inr ⟨d₂ - 1, by omega, by rw [hcast₂]⟩)
  have hmem : ∀ x ∈ S, x ≤ B ∨ C ≤ x := by
    intro x hx
    rcases (hS x).1 hx with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
    · left; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
    · right
      have h1 : j ≤ d₂ - 1 := by omega
      have h2 : (j : ℝ) ≤ ((d₂ - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [hcast₂] at h2; linarith
  obtain ⟨n, hn⟩ := hint _ hC _ hB
  rcases lt_trichotomy n 1 with h | h | h
  · exfalso
    have hn0 : n ≤ 0 := by omega
    have hn0' : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
    by_cases hCA : c₁ - e₁ ≤ C
    · have hk : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      have hk' : (((-n).toNat : ℕ) : ℝ) = -(n : ℝ) := by exact_mod_cast hk
      have hkd : (-n).toNat < d₁ := by
        have : (((-n).toNat : ℕ) : ℝ) < d₁ := by rw [hk']; linarith
        exact_mod_cast this
      refine hdisj (-n).toNat (d₂ - 1) hkd (by omega) ?_
      rw [hk', hcast₂]; linarith
    · rw [not_le] at hCA
      have hJ0 : (0 : ℤ) ≤ n + d₁ + d₂ - 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) + d₁ + d₂ - 2 := by linarith
        exact_mod_cast this
      have hJ1 : n + d₁ + d₂ - 2 < (d₂ : ℤ) := by
        have : (n : ℝ) + d₁ + d₂ - 2 < d₂ := by linarith
        exact_mod_cast this
      have hj : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℤ) = n + d₁ + d₂ - 2 := Int.toNat_of_nonneg hJ0
      have hj' : (((n + d₁ + d₂ - 2).toNat : ℕ) : ℝ) = (n : ℝ) + d₁ + d₂ - 2 := by exact_mod_cast hj
      have hjd : (n + d₁ + d₂ - 2).toNat < d₂ := by omega
      refine hdisj (d₁ - 1) (n + d₁ + d₂ - 2).toNat (by omega) hjd ?_
      rw [hj', hcast₁]; linarith
  · subst h
    push_cast at hn
    linarith
  · exfalso
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
    have hC1 : C - 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hB1 : B + 1 ∉ S := fun h1 => by rcases hmem _ h1 with h2 | h2 <;> linarith
    have hClt : C < 1 := by
      by_contra h3; exact hC1 (hP _ hC (not_lt.1 h3))
    have hBgt : -1 < B := by
      by_contra h3; rw [not_lt] at h3
      have h4 := hneg _ (hP _ (hneg _ hB) (by linarith))
      exact hB1 (by convert h4 using 1; ring)
    linarith
end PositivityTheory.Rg.Rs.StrStepA
