-- Prove2me | solution 1 for RobustBCPCVRP.Formulation.scaling_valid
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:21:02.514456+00:00
-- url     : https://prove2.me/submissions/da4fca00-04a6-4558-a982-04af55f353c7

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
set_option autoImplicit false
open LysgaardCVRP.Shrink RobustBCPCVRP.Formulation

theorem ll_load {n : ℕ} (d : Fin (n + 1) → ℕ) (g : ℕ) (hg : 0 < g) (r : List (Fin (n + 1))) :
    load d r ≤ g * load (fun v => ⌈(d v : ℚ) / g⌉₊) r := by
  induction r with
  | nil => simp [load]
  | cons a t ih =>
    simp only [load, List.map_cons, List.sum_cons] at ih ⊢
    have h1 : d a ≤ g * ⌈(d a : ℚ) / g⌉₊ := by
      have hgq : (0 : ℚ) < g := by exact_mod_cast hg
      have : (d a : ℚ) / g ≤ ⌈(d a : ℚ) / g⌉₊ := Nat.le_ceil _
      rw [div_le_iff₀ hgq] at this
      have : (d a : ℚ) ≤ (g * ⌈(d a : ℚ) / g⌉₊ : ℕ) := by push_cast; linarith
      exact_mod_cast this
    nlinarith

theorem solution {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (C g : ℕ) (hg : 1 < g) (r : List (Fin (n + 1)))
    (hr : IsQRoute E (fun v => ⌈(d v : ℚ) / g⌉₊) ⌊(C : ℚ) / g⌋₊ r) :
    IsQRoute E d C r := by
  obtain ⟨hw, hn, hl⟩ := hr
  refine ⟨hw, hn, ?_⟩
  have h1 := ll_load d g (by omega) r
  have h2 : g * ⌊(C : ℚ) / g⌋₊ ≤ C := by
    have hgq : (0 : ℚ) < g := by exact_mod_cast (by omega : 0 < g)
    have : ((⌊(C : ℚ) / g⌋₊ : ℕ) : ℚ) ≤ (C : ℚ) / g := Nat.floor_le (by positivity)
    rw [le_div_iff₀ hgq] at this
    have : ((⌊(C : ℚ) / g⌋₊ * g : ℕ) : ℚ) ≤ (C : ℚ) := by push_cast; exact this
    have := (Nat.cast_le (α := ℚ)).1 this
    linarith [Nat.mul_comm g ⌊(C : ℚ) / g⌋₊]
  have h3 : g * load (fun v => ⌈(d v : ℚ) / g⌉₊) r ≤ g * ⌊(C : ℚ) / g⌋₊ :=
    Nat.mul_le_mul_left g hl
  exact le_trans h1 (le_trans h3 h2)
