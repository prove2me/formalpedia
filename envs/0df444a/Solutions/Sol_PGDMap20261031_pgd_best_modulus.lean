-- Prove2me | solution 1 for PGDMap20261031.pgd_best_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:45:33.964602+00:00
-- url     : https://prove2.me/submissions/2252b99d-85b7-4f53-b47f-8b54a5bf8c3f

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_PGD

open PGDMap20261031

theorem solution : BestModulusClaim := by
  intro d r hr hnon
  have hzero : StrongPenalty r 0 := by
    intro x hx y hy t ht
    have hconv := hr.2.2.2 hx hy ht.1 (sub_nonneg.mpr ht.2) (by ring : t + (1 - t) = 1)
    simpa using hconv
  let S : Set ℝ := {μ | 0 ≤ μ ∧ StrongPenalty r μ}
  have hSne : S.Nonempty := ⟨0, le_rfl, hzero⟩
  have hSbd : BddAbove S := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnon
    let D := ‖x - y‖ ^ 2 / 8
    let R := (1 / 2 : ℝ) * r.value x + (1 - 1 / 2 : ℝ) * r.value y -
      r.value ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y)
    have hD : 0 < D := div_pos (sq_pos_of_pos (norm_sub_pos_iff.mpr hxy)) (by norm_num)
    refine ⟨R / D, ?_⟩
    intro μ hμ
    apply (le_div_iff₀ hD).2
    have h := hμ.2 x hx y hy (1 / 2) ⟨by norm_num, by norm_num⟩
    dsimp [D, R]
    nlinarith only [h]
  constructor
  · exact le_csSup hSbd (show 0 ∈ S from ⟨le_rfl, hzero⟩)
  · intro x hx y hy t ht
    let D := 1 / 2 * t * (1 - t) * ‖x - y‖ ^ 2
    let R := t * r.value x + (1 - t) * r.value y -
      r.value (t • x + (1 - t) • y)
    have hD : 0 ≤ D := by
      dsimp [D]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ht.1)
        (sub_nonneg.mpr ht.2)) (sq_nonneg _)
    have hR : 0 ≤ R := by
      have h := hzero x hx y hy t ht
      dsimp [R]
      nlinarith only [h]
    suffices h : bestModulus r * D ≤ R by
      dsimp [D, R] at h
      nlinarith only [h]
    by_cases hDzero : D = 0
    · simpa [hDzero] using hR
    · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDzero)
      apply (le_div_iff₀ hDpos).mp
      apply csSup_le hSne
      intro μ hμ
      apply (le_div_iff₀ hDpos).2
      have h := hμ.2 x hx y hy t ht
      dsimp [D, R]
      nlinarith only [h]
