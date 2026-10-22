-- Prove2me | solution 1 for TheoryOfGames.ThreePerson.solution_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:23.801407+00:00
-- url     : https://prove2.me/submissions/c97aaa93-d63e-403c-b799-c6699325ffa0

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution

set_option autoImplicit false
open TheoryOfGames.ThreePerson

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : TheoryOfGames.CharFun.IsCharFunction v)
    (V : Set (Fin n → ℝ)) (hV : IsSolution v V) : V.Nonempty := by
  obtain ⟨h0, hc, hs⟩ := hv
  have key : ∀ S : Finset (Fin n), ∑ i ∈ S, v {i} ≤ v S := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [h0]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      have h := hs {a} S (by simpa using ha)
      rw [← Finset.insert_eq] at h
      linarith
  have huniv : v Finset.univ = 0 := by
    have := hc ∅
    rw [Finset.compl_empty, h0] at this
    linarith
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = -∑ i, v {i} := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by
    have := key Finset.univ
    rw [huniv] at this
    linarith
  have himp : IsImputation v (fun i => v {i} + δ / n) := by
    constructor
    · intro i
      have : 0 ≤ δ / (n : ℝ) := div_nonneg hδ0 (Nat.cast_nonneg n)
      show v {i} ≤ v {i} + δ / n
      linarith
    · show ∑ i, (v {i} + δ / n) = 0
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hn : (n : ℝ) ≠ 0 := by positivity
        have : (n : ℝ) * (δ / n) = δ := by field_simp
        rw [this]
        linarith
  obtain ⟨a, ha, _⟩ := hV.2.2 _ himp (by rw [hne]; simp)
  rw [hne] at ha
  exact ha
