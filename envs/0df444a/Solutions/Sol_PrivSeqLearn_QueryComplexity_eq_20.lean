-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:48:51.545151+00:00
-- url     : https://prove2.me/submissions/aaa726d3-8334-4457-96dd-249186406a58

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_SpecialIntervals

set_option autoImplicit false
open PrivSeqLearn.QueryComplexity

lemma psl_hist_congr {N : ℕ} (φ : Strategy N) (x x' : ℝ) (y : Fin φ.Ybar)
    (h : ∀ k : Fin N, decide (queries φ x y k ≤ x') = decide (queries φ x y k ≤ x)) :
    ∀ k, k ≤ N → hist φ x' y k = hist φ x y k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hk' : k < N := hk
    have e := ih hk'.le
    have h2 : decide (φ.query (hist φ x y k) y ≤ x') = decide (φ.query (hist φ x y k) y ≤ x) :=
      h ⟨k, hk'⟩
    show hist φ x' y k ++ [decide (φ.query (hist φ x' y k) y ≤ x')] =
      hist φ x y k ++ [decide (φ.query (hist φ x y k) y ≤ x)]
    rw [e, h2]

lemma psl_final {N : ℕ} (ϵ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) (y : Fin φ.Ybar) (a b : ℝ)
    (hax : a ≤ x) (hxb : x < b)
    (hcons : ∀ w ∈ queryPoints (queries φ x y), w ≤ a ∨ b ≤ w) :
    b - a ≤ ϵ := by
  have ha0 : 0 ≤ a := by
    have h0 : (0 : ℝ) ∈ queryPoints (queries φ x y) := by simp [queryPoints]
    rcases hcons 0 h0 with h | h
    · exact h
    · exfalso; linarith [hx.1]
  have hb1 : b ≤ 1 := by
    have h1 : (1 : ℝ) ∈ queryPoints (queries φ x y) := by simp [queryPoints]
    rcases hcons 1 h1 with h | h
    · exfalso; linarith [hx.2]
    · exact h
  have hsame : ∀ x' ∈ Set.Ico a b, ∀ k : Fin N,
      decide (queries φ x y k ≤ x') = decide (queries φ x y k ≤ x) := by
    intro x' hx' k
    have hk : queries φ x y k ∈ queryPoints (queries φ x y) := by simp [queryPoints]
    rcases hcons _ hk with h | h
    · have h1 : queries φ x y k ≤ x' := h.trans hx'.1
      have h2 : queries φ x y k ≤ x := h.trans hax
      simp [h1, h2]
    · have h1 : ¬ queries φ x y k ≤ x' := not_le.2 (lt_of_lt_of_le hx'.2 h)
      have h2 : ¬ queries φ x y k ≤ x := not_le.2 (lt_of_lt_of_le hxb h)
      simp [h1, h2]
  have hest : ∀ x' ∈ Set.Ico a b, estimate φ x' y = estimate φ x y := by
    intro x' hx'
    unfold estimate
    rw [psl_hist_congr φ x x' y (hsame x' hx') N le_rfl]
  have hacc' : ∀ x' ∈ Set.Ico a b, |estimate φ x y - x'| ≤ ϵ / 2 := by
    intro x' hx'
    have := hacc x' ⟨ha0.trans hx'.1, hx'.2.trans_le hb1⟩ y
    rw [hest x' hx'] at this
    exact this
  by_contra hlt
  push_neg at hlt
  have h1 := hacc' a ⟨le_rfl, by linarith [hlt, hax, hxb]⟩
  have hϵ : 0 ≤ ϵ := by linarith [abs_nonneg (estimate φ x y - a)]
  have hx' : (a + ϵ + b) / 2 ∈ Set.Ico a b := ⟨by linarith, by linarith⟩
  have h2 := hacc' _ hx'
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

theorem solution {N : ℕ} (ϵ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ) (q : Fin N → ℝ) :
    infoSet φ q ⊆ specialUnion ϵ q := by
  rintro x ⟨hx, y, rfl⟩
  have hfin : (queryPoints (queries φ x y)).Finite :=
    ((Set.finite_range _).insert 1).insert 0
  have h0 : (0 : ℝ) ∈ queryPoints (queries φ x y) := by simp [queryPoints]
  have h1 : (1 : ℝ) ∈ queryPoints (queries φ x y) := by simp [queryPoints]
  have hne1 : {w ∈ queryPoints (queries φ x y) | w ≤ x}.Nonempty := ⟨0, h0, hx.1⟩
  have hne2 : {w ∈ queryPoints (queries φ x y) | x < w}.Nonempty := ⟨1, h1, hx.2⟩
  obtain ⟨a, ⟨ha, hax⟩, hamax⟩ := Set.exists_max_image _ id (hfin.subset (fun w hw => hw.1)) hne1
  obtain ⟨b, ⟨hb, hxb⟩, hbmin⟩ := Set.exists_min_image _ id (hfin.subset (fun w hw => hw.1)) hne2
  have hcons : ∀ w ∈ queryPoints (queries φ x y), w ≤ a ∨ b ≤ w := by
    intro w hw
    by_cases hwx : w ≤ x
    · exact Or.inl (hamax w ⟨hw, hwx⟩)
    · exact Or.inr (hbmin w ⟨hw, not_le.1 hwx⟩)
  have hle := psl_final ϵ φ hacc x hx y a b hax hxb hcons
  simp only [specialUnion, Set.mem_iUnion]
  exact ⟨a, b, ⟨ha, hb, lt_of_le_of_lt hax hxb, hle, hcons⟩, hax, hxb⟩
