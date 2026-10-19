-- Prove2me | solution 1 for SoficGroups.shifted_floor_drop_volume_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/c5fd30f5-4ede-4cc7-8e1c-48cbdddf20e8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_shifted_floor_drop_subset_two_intervals

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (u v H : ℝ) (hH : 0 < H) (hvu : v ≤ u) :
    MeasureTheory.volume
        {r : ℝ | r ∈ Set.Ico 0 H ∧
          ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ≤
      ENNReal.ofReal (u - v) := by
  let k : ℤ := ⌊u / H⌋
  let c : ℝ := (((k + 1 : ℤ) : ℝ) * H - u)
  let d : ℝ := u - v
  have hd : 0 ≤ d := sub_nonneg.mpr hvu
  have hklo : (k : ℝ) ≤ u / H := by
    dsimp [k]
    exact Int.floor_le _
  have hkhi : u / H < (k : ℝ) + 1 := by
    dsimp [k]
    exact Int.lt_floor_add_one _
  have hklo' : (k : ℝ) * H ≤ u := (le_div_iff₀ hH).mp hklo
  have hkhi' : u < ((k : ℝ) + 1) * H := (div_lt_iff₀ hH).mp hkhi
  have hc0 : 0 ≤ c := by
    dsimp [c]
    push_cast
    linarith
  have hcH : c ≤ H := by
    dsimp [c]
    push_cast
    linarith
  let A : Set ℝ := Set.Ico 0 (max 0 (c - H + d))
  let B : Set ℝ := Set.Ico c (min H (c + d))
  have hsubset :
      {r : ℝ | r ∈ Set.Ico 0 H ∧
        ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ⊆ A ∪ B := by
    intro r hr
    have htwo := shifted_floor_drop_subset_two_intervals u v H hH k rfl hr
    rcases htwo with hleft | hright
    · left
      change r ∈ Set.Ico 0 (max 0 (c - H + d))
      refine ⟨hr.1.1, ?_⟩
      apply lt_of_lt_of_le (b := c - H + d)
      · have hupper := hleft.2
        dsimp [c, d]
        push_cast
        linarith
      · exact le_max_right _ _
    · right
      change r ∈ Set.Ico c (min H (c + d))
      refine ⟨?_, lt_min hr.1.2 ?_⟩
      · have hlower := hright.1
        dsimp [c]
        exact hlower
      · have hupper := hright.2
        dsimp [c, d]
        push_cast at hupper ⊢
        linarith
  have hA : MeasureTheory.volume A =
      ENNReal.ofReal (max 0 (c - H + d)) := by
    dsimp [A]
    rw [Real.volume_Ico, sub_zero]
  have hB : MeasureTheory.volume B =
      ENNReal.ofReal (min H (c + d) - c) := by
    dsimp [B]
    rw [Real.volume_Ico]
  have hA0 : 0 ≤ max 0 (c - H + d) := le_max_left _ _
  have hB0 : 0 ≤ min H (c + d) - c := by
    apply sub_nonneg.mpr
    exact le_min hcH (by linarith)
  have hlength : max 0 (c - H + d) + (min H (c + d) - c) = d := by
    by_cases hshort : d ≤ H - c
    · rw [max_eq_left (by linarith), min_eq_right (by linarith)]
      ring
    · have hlong : H - c < d := lt_of_not_ge hshort
      rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      ring
  calc
    MeasureTheory.volume
        {r : ℝ | r ∈ Set.Ico 0 H ∧
          ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ≤
        MeasureTheory.volume (A ∪ B) :=
      MeasureTheory.measure_mono hsubset
    _ ≤ MeasureTheory.volume A + MeasureTheory.volume B :=
      MeasureTheory.measure_union_le A B
    _ = ENNReal.ofReal (max 0 (c - H + d)) +
        ENNReal.ofReal (min H (c + d) - c) := by rw [hA, hB]
    _ = ENNReal.ofReal d := by
      rw [← ENNReal.ofReal_add hA0 hB0, hlength]
    _ = ENNReal.ofReal (u - v) := by rfl
end SoficGroups
