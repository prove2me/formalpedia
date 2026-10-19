-- Prove2me | solution 1 for SoficGroups.shifted_floor_drop_subset_two_intervals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/a543e565-96e6-462e-8381-26ea330e9d3c

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (u v H : ℝ) (hH : 0 < H) (k : ℤ) (hk : k = ⌊u / H⌋) :
    {r : ℝ | r ∈ Set.Ico 0 H ∧ ⌊(v + r) / H⌋ < ⌊(u + r) / H⌋} ⊆
      Set.Ico ((k : ℝ) * H - u) ((k : ℝ) * H - v) ∪
        Set.Ico (((k + 1 : ℤ) : ℝ) * H - u)
          (((k + 1 : ℤ) : ℝ) * H - v) := by
  intro r hr
  rcases hr with ⟨⟨hr0, hrH⟩, hdrop⟩
  let j : ℤ := ⌊(u + r) / H⌋
  have hlow : k ≤ j := by
    rw [hk]
    apply Int.floor_mono
    apply (div_le_div_iff_of_pos_right hH).2
    linarith
  have hhigh : j < k + 2 := by
    apply Int.floor_lt.mpr
    have hu : u / H < (k : ℝ) + 1 := by
      rw [hk]
      exact Int.lt_floor_add_one (u / H)
    have hr' : r / H < 1 := (div_lt_one hH).mpr hrH
    calc
      (u + r) / H = u / H + r / H := by ring
      _ < ((k : ℝ) + 1) + 1 := add_lt_add hu hr'
      _ = ((k + 2 : ℤ) : ℝ) := by push_cast; ring
  have hcases : j = k ∨ j = k + 1 := by omega
  have hv : (v + r) / H < (j : ℝ) := by
    apply Int.floor_lt.mp
    exact hdrop
  have hu : (j : ℝ) ≤ (u + r) / H := Int.floor_le _
  have hv' : v + r < (j : ℝ) * H := (div_lt_iff₀ hH).mp hv
  have hu' : (j : ℝ) * H ≤ u + r := (le_div_iff₀ hH).mp hu
  rcases hcases with hcase | hcase
  · left
    rw [hcase] at hv' hu'
    exact ⟨by linarith, by linarith⟩
  · right
    rw [hcase] at hv' hu'
    exact ⟨by linarith, by linarith⟩
end SoficGroups
