-- Prove2me | solution 1 for ServiceParts.Allocation.slope_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:28:46.541931+00:00
-- url     : https://prove2.me/submissions/8e35ccbf-47ac-4fd9-b079-e9318ca6a99d

import Mathlib
import Definitions.Def_ServiceParts_Allocation_AllocData

set_option autoImplicit false

open ServiceParts.Allocation in
theorem slope_monotone_grid_nonneg {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed)
    (m : Fin Mbar) : ∀ j : ℕ, j ≤ d.n m → (0 : ℤ) ≤ d.grid m j := by
  intro j
  induction j with
  | zero => intro _; rw [hd.grid_zero m]
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := hd.grid_strictMono m j (by omega)
    omega

open ServiceParts.Allocation in
theorem solution {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed)
    (m : Fin Mbar) (k : ℕ) (hk : k < d.n m) :
    d.slope m k ≤ d.slope m (k + 1) := by
  by_cases hk1 : k + 1 < d.n m
  · obtain ⟨φ, hφ, hc⟩ := hd.cost_convex m
    unfold AllocData.slope
    rw [if_pos hk, if_pos hk1]
    rw [hc k (by omega), hc (k + 1) (by omega), hc (k + 1 + 1) (by omega)]
    have g0 := slope_monotone_grid_nonneg d hd m k (by omega)
    have g2 := slope_monotone_grid_nonneg d hd m (k + 1 + 1) (by omega)
    have s1 := hd.grid_strictMono m k hk
    have s2 := hd.grid_strictMono m (k + 1) hk1
    have hx : ((d.grid m k : ℤ) : ℝ) ∈ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici]; exact_mod_cast g0
    have hz : ((d.grid m (k + 1 + 1) : ℤ) : ℝ) ∈ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici]; exact_mod_cast g2
    exact hφ.slope_mono_adjacent hx hz (by exact_mod_cast s1) (by exact_mod_cast s2)
  · have hkn : k + 1 = d.n m := by omega
    unfold AllocData.slope
    rw [if_pos hk, if_neg hk1]
    have : d.n m - 1 = k := by omega
    rw [this, hkn]
