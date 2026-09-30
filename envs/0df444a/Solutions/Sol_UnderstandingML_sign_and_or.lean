-- Prove2me | solution 1 for UnderstandingML.sign_and_or
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T07:02:31.797989+00:00
-- url     : https://prove2.me/submissions/a4db3dc0-3b5c-4bb6-b160-22f99408ab79

import Definitions.Def_UnderstandingML_NeuralNetworks

open MeasureTheory
open scoped BigOperators

-- Lemma 20.4 (p. 273): a sign neuron implements conjunction and disjunction.
--
-- The book reads a neuron output as `±1`.  With `S = ∑ᵢ (if x i then 1 else -1)` the
-- chapter's formulas are `∧ᵢ xᵢ = sign (1 - k + S)` and `∨ᵢ xᵢ = sign (k - 1 + S)`, so the
-- conjunction is realised exactly when `1 - k + S > 0` and the disjunction exactly when
-- `k - 1 + S > 0`.  The published statement asserts both equivalences.
--
-- The proof is a count.  Let `T = {i | x i = true}` and `F = {i | ¬ x i}`.  Then
-- `|T| + |F| = k` (Finset.card_filter_add_card_filter_not) and `S = |T| - |F|`, so
--
--   * `1 - k + S = 1 - 2 * |F|`, positive exactly when `|F| = 0`, i.e. every input is `+1`;
--   * `k - 1 + S = 2 * |T| - 1`, positive exactly when `|T| ≥ 1`, i.e. some input is `+1`.
--
-- The two counts are `Finset.sum_boole` (Mathlib/Algebra/BigOperators/Ring/Finset.lean:44),
-- `(∑ x ∈ s, if p x then 1 else 0) = #{x ∈ s | p x}`, one applied to `p = (x · = true)` and
-- the other to `p = (x · = false)`; the second is stated with the predicate `x i = false`
-- because the coefficient is `1` exactly there, and `x i = false ↔ ¬ (x i = true)` is closed
-- by `Finset.ext` + `cases`.
--
-- The only genuine inequality is `1 - 2d > 0 → d = 0`, discharged by exhibiting `i ∈ F`
-- to force `1 ≤ F.card` (Finset.card_le_card on Finset.singleton_subset_iff) and then
-- `linarith` against the cast bound.  `k = 0` needs no case split: the conjunction is
-- vacuous, `S = 0`, and `d = 0` satisfies `1 - 2d > 0`.

theorem solution (k : ℕ) (x : Fin k → Bool) :
    (0 < 1 - (k : ℝ) + ∑ i, (if x i then (1 : ℝ) else -1) ↔ ∀ i, x i = true) ∧
    (0 < (k : ℝ) - 1 + ∑ i, (if x i then (1 : ℝ) else -1) ↔ ∃ i, x i = true) := by
  classical
  have hpart : (Finset.univ.filter fun i => x i).card
      + (Finset.univ.filter fun i => ¬ x i).card = k := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
      (p := fun i => x i = true)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hpartR : ((Finset.univ.filter fun i => x i).card : ℝ)
      + ((Finset.univ.filter fun i => ¬ x i).card : ℝ) = (k : ℝ) := by
    exact_mod_cast hpart
  -- S = |T| - |F|
  have hT : (∑ i : Fin k, (if x i then (1 : ℝ) else 0) : ℝ)
      = ((Finset.univ.filter fun i => x i).card : ℝ) := by
    simp only [Finset.sum_boole]
  have hF : (∑ i : Fin k, (if x i then (0 : ℝ) else 1) : ℝ)
      = ((Finset.univ.filter fun i => ¬ x i).card : ℝ) := by
    have hone : ∀ i : Fin k, (if x i then (0 : ℝ) else 1)
        = if x i = false then (1 : ℝ) else 0 := by
      intro i
      cases hi : x i <;> simp [hi]
    rw [Finset.sum_congr rfl fun i _ => hone i]
    rw [Finset.sum_boole]
    have hfilter : (Finset.univ.filter fun i => x i = false)
        = Finset.univ.filter fun i => ¬ x i := by
      ext i
      cases hi : x i <;> simp [hi]
    rw [hfilter]
  have hone : ∀ i : Fin k, (if x i then (1 : ℝ) else -1)
      = (if x i then (1 : ℝ) else 0) - (if x i then (0 : ℝ) else 1) := by
    intro i
    cases hi : x i <;> simp [hi]
  have hS : (∑ i : Fin k, (if x i then (1 : ℝ) else -1) : ℝ)
      = 2 * (Finset.univ.filter fun i => x i).card - k := by
    calc (∑ i : Fin k, (if x i then (1 : ℝ) else -1) : ℝ)
        = ∑ i : Fin k, ((if x i then (1 : ℝ) else 0) - (if x i then (0 : ℝ) else 1)) :=
          Finset.sum_congr rfl fun i _ => hone i
      _ = (∑ i : Fin k, (if x i then (1 : ℝ) else 0) : ℝ)
          - ∑ i : Fin k, (if x i then (0 : ℝ) else 1) := by
        simp only [Finset.sum_sub_distrib]
      _ = 2 * (Finset.univ.filter fun i => x i).card - k := by rw [hT, hF]; linarith
  constructor
  · rw [hS]
    constructor
    · intro hpos i
      by_contra hnotx
      have hmem : i ∈ Finset.univ.filter (fun j => ¬ x j) :=
        (Finset.mem_filter).2 ⟨Finset.mem_univ i, hnotx⟩
      have hle : (1 : ℕ) ≤ (Finset.univ.filter (fun j => ¬ x j)).card :=
        Finset.card_le_card (Finset.singleton_subset_iff.mpr hmem)
      have hleR : (1 : ℝ) ≤ ((Finset.univ.filter (fun j => ¬ x j)).card : ℝ) := by
        exact_mod_cast hle
      linarith
    · intro hall
      have hFc : ((Finset.univ.filter (fun j => ¬ x j)).card : ℝ) = 0 := by
        have hempty : Finset.univ.filter (fun j => ¬ x j) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro j _ hjnotx
          exact absurd (hall j) hjnotx
        rw [hempty, Finset.card_empty]
        exact_mod_cast rfl
      -- `1 - ↑k + (2 * ↑|T| - ↑k) = 1 - 2 * ↑|F|` by `hpartR`.
      have hkey : (1 : ℝ) - (k : ℝ) + (2 * ((Finset.univ.filter fun i => x i).card : ℝ) - (k : ℝ))
          = 1 - 2 * ((Finset.univ.filter fun j => ¬ x j).card : ℝ) := by
        linarith
      rw [hkey, hFc]
      linarith
  · rw [hS]
    constructor
    · intro hpos
      have hposR : (0 : ℝ) < ((Finset.univ.filter fun i => x i).card : ℝ) := by linarith
      have hcard : 0 < (Finset.univ.filter fun i => x i).card := by exact_mod_cast hposR
      rw [Finset.card_pos] at hcard
      obtain ⟨i, hi⟩ := Finset.filter_nonempty_iff.mp hcard
      exact ⟨i, hi.2⟩
    · rintro ⟨i, hi⟩
      have hmem : i ∈ Finset.univ.filter (fun j => x j) :=
        (Finset.mem_filter).2 ⟨Finset.mem_univ i, hi⟩
      have hle : (1 : ℕ) ≤ (Finset.univ.filter fun j => x j).card :=
        Finset.card_le_card (Finset.singleton_subset_iff.mpr hmem)
      have hleR : (1 : ℝ) ≤ ((Finset.univ.filter fun j => x j).card : ℝ) := by
        exact_mod_cast hle
      linarith
