-- Prove2me | solution 1 for ThreeOpSplitting.Accel.stepsize_identity_part2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:18:19.849577+00:00
-- url     : https://prove2.me/submissions/dcbbc53e-393a-477f-9aea-1108db4eb6f3

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_Stepsizes

open Filter Topology
open ThreeOpSplitting.Accel

/-- The stepsizes (3.7) stay in `(0, 2μ_B/L_C²)`; this is what makes the radicand `> 1`. -/
private theorem inv2 (μB LC γ0 : ℝ) (_hμB : 0 < μB) (hLC : 0 < LC) (hγ0 : 0 < γ0)
    (hγ0' : γ0 < 2 * μB / LC ^ 2) :
    ∀ k, 0 < stepsPart2 μB LC γ0 k ∧ stepsPart2 μB LC γ0 k < 2 * μB / LC ^ 2 := by
  have hL2 : (0:ℝ) < LC ^ 2 := by positivity
  intro k
  induction k with
  | zero => exact ⟨hγ0, hγ0'⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hmul : stepsPart2 μB LC γ0 k * LC ^ 2 < 2 * μB := (lt_div_iff₀ hL2).mp h2
    have hpos : 0 < μB - stepsPart2 μB LC γ0 k * LC ^ 2 / 2 := by linarith
    have hR : 1 < 1 + 2 * stepsPart2 μB LC γ0 k * (μB - stepsPart2 μB LC γ0 k * LC ^ 2 / 2) := by
      nlinarith
    have hs1 : 1 < Real.sqrt (1 + 2 * stepsPart2 μB LC γ0 k *
        (μB - stepsPart2 μB LC γ0 k * LC ^ 2 / 2)) := by
      have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hR
      simpa using this
    have heq : stepsPart2 μB LC γ0 (k + 1) = stepsPart2 μB LC γ0 k /
        Real.sqrt (1 + 2 * stepsPart2 μB LC γ0 k *
          (μB - stepsPart2 μB LC γ0 k * LC ^ 2 / 2)) := rfl
    rw [heq]
    refine ⟨by positivity, ?_⟩
    calc stepsPart2 μB LC γ0 k / Real.sqrt (1 + 2 * stepsPart2 μB LC γ0 k *
            (μB - stepsPart2 μB LC γ0 k * LC ^ 2 / 2)) < stepsPart2 μB LC γ0 k := by
          rw [div_lt_iff₀ (by linarith)]
          nlinarith
      _ < 2 * μB / LC ^ 2 := h2

theorem solution (μB LC γ0 : ℝ)
    (hμB : 0 < μB) (hLC : 0 < LC) (hγ0 : 0 < γ0) (hγ0' : γ0 < 2 * μB / LC ^ 2) (k : ℕ) :
    1 / stepsPart2 μB LC γ0 (k + 1) ^ 2
      = (1 + 2 * stepsPart2 μB LC γ0 k * (μB - stepsPart2 μB LC γ0 k * LC ^ 2 / 2))
        / stepsPart2 μB LC γ0 k ^ 2 := by
  have hL2 : (0:ℝ) < LC ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := inv2 μB LC γ0 hμB hLC hγ0 hγ0' k
  have hmul : stepsPart2 μB LC γ0 k * LC ^ 2 < 2 * μB := (lt_div_iff₀ hL2).mp h2
  have hpos : 0 < μB - stepsPart2 μB LC γ0 k * LC ^ 2 / 2 := by linarith
  set g := stepsPart2 μB LC γ0 k with hgdef
  set R := 1 + 2 * g * (μB - g * LC ^ 2 / 2) with hRdef
  have hR : 0 < R := by rw [hRdef]; nlinarith
  have heq : stepsPart2 μB LC γ0 (k + 1) = g / Real.sqrt R := rfl
  have hsq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hsp : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  rw [heq, div_pow, hsq]
  rw [one_div_div]
