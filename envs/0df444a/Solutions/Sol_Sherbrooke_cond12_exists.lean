-- Prove2me | solution 1 for Sherbrooke.cond12_exists
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:36:50.834431+00:00
-- url     : https://prove2.me/submissions/b6db680e-9c62-4386-aa60-ac519c209bb7

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12

open Sherbrooke in
theorem solution (c : ℝ) (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) (hc : 0 ≤ c)
    (hcorr : 0 < c ∨ ∃ m₀ : ℕ, ∀ k : ℕ, Ξ m₀ ≤ Ξ k) :
    ∃ m : ℕ, Sherbrooke.Cond12 c Ξ m := by
  classical
  obtain ⟨B, hB⟩ := hbdd
  have hne : ∀ m : ℕ, {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧
      y = a * (m : ℝ) + b}.Nonempty := by
    intro m
    exact ⟨0 * (m : ℝ) + B, 0, B, fun k => by
      have := hB ⟨k, rfl⟩
      simpa using this, rfl⟩
  have hbd : ∀ m : ℕ, BddAbove {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧
      y = a * (m : ℝ) + b} := by
    intro m
    refine ⟨Ξ m, ?_⟩
    rintro y ⟨a, b, h, rfl⟩
    exact h m
  have hle : ∀ (m : ℕ) (a b : ℝ), (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) →
      a * (m : ℝ) + b ≤ Sherbrooke.lowerHull Ξ m :=
    fun m a b h => le_csSup (hbd m) ⟨a, b, h, rfl⟩
  have hLle : ∀ m, Sherbrooke.lowerHull Ξ m ≤ Ξ m := by
    intro m
    refine csSup_le (hne m) ?_
    rintro y ⟨a, b, h, rfl⟩
    exact h m
  have hLge : ∀ m, B ≤ Sherbrooke.lowerHull Ξ m := by
    intro m
    have := hle m 0 B (fun k => by
      have := hB ⟨k, rfl⟩
      simpa using this)
    simpa using this
  have hex : ∃ m, 0 ≤ c + Sherbrooke.lowerHull Ξ (m + 1) - Sherbrooke.lowerHull Ξ m := by
    rcases hcorr with hcpos | ⟨m₀, hm₀⟩
    · by_contra hno
      push_neg at hno
      have hdec : ∀ m : ℕ, Sherbrooke.lowerHull Ξ m ≤ Sherbrooke.lowerHull Ξ 0 - c * m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          have := hno m
          push_cast
          linarith
      obtain ⟨m, hm⟩ := exists_nat_gt ((Sherbrooke.lowerHull Ξ 0 - B) / c)
      have h1 := hdec m
      have h2 := hLge m
      rw [div_lt_iff₀ hcpos] at hm
      nlinarith
    · refine ⟨m₀, ?_⟩
      have h1 : Ξ m₀ ≤ Sherbrooke.lowerHull Ξ (m₀ + 1) := by
        have := hle (m₀ + 1) 0 (Ξ m₀) (fun k => by simpa using hm₀ k)
        simpa using this
      have h2 := hLle m₀
      linarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  by_cases h0 : Nat.find hex = 0
  · exact Or.inl h0
  · right
    have hlt : Nat.find hex - 1 < Nat.find hex := by omega
    have hnot := Nat.find_min hex hlt
    push_neg at hnot
    have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [e] at hnot
    linarith
