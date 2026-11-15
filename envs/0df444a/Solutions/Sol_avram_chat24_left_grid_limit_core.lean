-- Prove2me | solution 1 for avram_chat24_left_grid_limit_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:20:49.426096+00:00
-- url     : https://prove2.me/submissions/fe66cb76-061f-4b26-b424-b23fdc946436

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology NNReal

noncomputable section

/-- The predecessor cell of a uniform floor grid converges to a positive
time, and every selected left endpoint is strictly earlier. -/
private theorem left_grid_convergence_aux (t : ℝ≥0) (ht : 0 < t) :
    let u : ℕ → ℝ≥0 := fun n =>
      ((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1 : ℕ) : ℝ≥0) /
        ((n + 1 : ℕ) : ℝ≥0)
    Tendsto u atTop (𝓝[<] t) := by
  let u : ℕ → ℝ≥0 := fun n =>
    ((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1 : ℕ) : ℝ≥0) /
      ((n + 1 : ℕ) : ℝ≥0)
  have htR : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr ht
  have hFloorTop : Tendsto
      (fun n : ℕ => ⌊(t : ℝ) * (((n + 1 : ℕ) : ℝ))⌋₊)
      atTop atTop := by
    exact (tendsto_nat_floor_mul_atTop (t : ℝ) htR).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hFloorPos : ∀ᶠ n : ℕ in atTop,
      0 < ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ := by
    simpa only [mul_comm] using
      hFloorTop.eventually (eventually_gt_atTop (0 : ℕ))
  have hDenTop : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)))
      atTop (atTop : Filter ℝ) :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hFloorRatio : Tendsto
      (fun n : ℕ => (((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ)) /
        (((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (t : ℝ)) := by
    convert ((tendsto_nat_floor_mul_div_atTop (a := (t : ℝ))
      (le_of_lt htR)).comp hDenTop) using 1
    funext n
    simp only [Function.comp_def, mul_comm]
  have hInv : Tendsto (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hEq : ∀ᶠ n : ℕ in atTop,
      ((((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1 : ℕ) : ℝ)) /
        (((n + 1 : ℕ) : ℝ))) =
      ((((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ)) /
        (((n + 1 : ℕ) : ℝ))) -
      1 / (((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [hFloorPos] with n hn
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hn)]
    ring
  have hReal : Tendsto
      (fun n : ℕ =>
        (((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1 : ℕ) : ℝ)) /
          (((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (t : ℝ)) := by
    apply (Filter.tendsto_congr' hEq).2
    simpa only [sub_zero] using hFloorRatio.sub hInv
  have hu : Tendsto u atTop (𝓝 t) := by
    apply NNReal.tendsto_coe.mp
    convert hReal using 1
    ext n
    simp only [u, NNReal.coe_div, NNReal.coe_natCast]
  have hBefore (n : ℕ) : u n < t := by
    have hd : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) := by positivity
    have hA : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) * (t : ℝ)) :=
      le_of_lt (mul_pos hd htR)
    have hFloorBound : ((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) ≤
        (((n + 1 : ℕ) : ℝ) * (t : ℝ)) := Nat.floor_le hA
    have hSub : ((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1 : ℕ) : ℝ) <
        (((n + 1 : ℕ) : ℝ) * (t : ℝ)) := by
      by_cases hz : ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ = 0
      · have hZero :
            (⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1 : ℕ) = 0 := by
          omega
        rw [hZero]
        simpa using mul_pos hd htR
      · have hn : (⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1) <
          ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ :=
          Nat.sub_lt (Nat.pos_of_ne_zero hz) (by decide)
        have hCast :
            (((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1 : ℕ) : ℝ)) <
              ((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast hn
        exact hCast.trans_le hFloorBound
    have hRat : ((((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1 : ℕ) : ℝ)) /
        (((n + 1 : ℕ) : ℝ))) < (t : ℝ) := by
      apply (div_lt_iff₀ hd).2
      simpa only [mul_comm] using hSub
    apply NNReal.coe_lt_coe.mp
    simpa only [u, NNReal.coe_div, NNReal.coe_natCast] using hRat
  exact tendsto_nhdsWithin_iff.mpr
    ⟨hu, Filter.Eventually.of_forall hBefore⟩

/-- The left predecessor grid is cofinal at the specified positive clock. -/
theorem solution (t : ℝ≥0) (ht : 0 < t) :
    let u : ℕ → ℝ≥0 := fun n =>
      ((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ - 1 : ℕ) : ℝ≥0) /
        ((n + 1 : ℕ) : ℝ≥0)
    Tendsto u atTop (𝓝[<] t) := by
  exact left_grid_convergence_aux t ht
