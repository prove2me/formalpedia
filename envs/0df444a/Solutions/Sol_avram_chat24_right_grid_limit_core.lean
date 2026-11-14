-- Prove2me | solution 1 for avram_chat24_right_grid_limit_core
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-13T14:40:27.793842+00:00
-- url     : https://prove2.me/submissions/47278afb-c073-4891-8259-a8ffd182a5b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem solution (t : ℝ≥0) :
    let u : ℕ → ℝ≥0 := fun n =>
      ((⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0) /
        ((n + 1 : ℕ) : ℝ≥0)
    Tendsto u atTop (𝓝[Ici t] t) := by
  intro u
  have hu_ge : ∀ n, t ≤ u n := by
    intro n
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    set x : ℝ := ((n + 1 : ℕ) : ℝ) * (t : ℝ)
    have hlt : x < (↑(⌊x⌋₊ + 1) : ℝ) := by
      have := Nat.lt_floor_add_one x
      simpa [Nat.cast_add, Nat.cast_one] using this
    have : (t : ℝ) ≤ (u n : ℝ) := by
      dsimp [u]
      have hxdiv : x / ((n + 1 : ℕ) : ℝ) = (t : ℝ) := by
        dsimp [x]; field_simp
      have hle : x / ((n + 1 : ℕ) : ℝ)
          ≤ (↑(⌊x⌋₊ + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (le_of_lt hlt) (le_of_lt hN)
      change (t : ℝ) ≤ (↑(⌊x⌋₊ + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)
      calc (t : ℝ) = x / ((n + 1 : ℕ) : ℝ) := hxdiv.symm
        _ ≤ (↑(⌊x⌋₊ + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) := hle
    exact_mod_cast this
  have hsqueeze : ∀ n,
      (t : ℝ) ≤ (u n : ℝ) ∧ (u n : ℝ) ≤ (t : ℝ) + 1 / ((n : ℝ) + 1) := by
    intro n
    refine ⟨by exact_mod_cast (hu_ge n), ?_⟩
    have hN : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
    set x : ℝ := ((n + 1 : ℕ) : ℝ) * (t : ℝ)
    have hx0 : 0 ≤ x := by positivity
    have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    have hle : (↑(⌊x⌋₊ + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)
        ≤ x / ((n + 1 : ℕ) : ℝ) + 1 / ((n : ℝ) + 1) := by
      have : (↑(⌊x⌋₊ + 1) : ℝ) ≤ x + 1 := by
        simpa [Nat.cast_add, Nat.cast_one] using (add_le_add_right hfloor 1)
      have h := div_le_div_of_nonneg_right this hN
      convert h using 1
      · rfl
      · simp [Nat.cast_add, Nat.cast_one]; ring
    have hxdiv : x / ((n + 1 : ℕ) : ℝ) = (t : ℝ) := by
      dsimp [x]; field_simp
    dsimp [u]
    change (↑(⌊x⌋₊ + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ (t : ℝ) + 1 / ((n : ℝ) + 1)
    calc (↑(⌊x⌋₊ + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)
        ≤ x / ((n + 1 : ℕ) : ℝ) + 1 / ((n : ℝ) + 1) := hle
      _ = (t : ℝ) + 1 / ((n : ℝ) + 1) := by rw [hxdiv]
  have htend : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 (t : ℝ)) := by
    have hlow : Tendsto (fun _ : ℕ => (t : ℝ)) atTop (𝓝 (t : ℝ)) := tendsto_const_nhds
    have hup0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hup : Tendsto (fun n : ℕ => (t : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
      have h := hlow.add hup0
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup
      (fun n => (hsqueeze n).1) (fun n => (hsqueeze n).2)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (NNReal.tendsto_coe).1 htend
  · filter_upwards with n using hu_ge n
end
