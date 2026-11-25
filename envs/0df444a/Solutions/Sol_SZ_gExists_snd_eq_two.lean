-- Prove2me | solution 1 for SZ.gExists_snd_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:19.474148+00:00
-- url     : https://prove2.me/submissions/1f3d0a08-2abd-4266-8f4a-789f30e8ed04

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_gVal_pos
import Theorems.Thm_SZ_gVal_ne_three
import Theorems.Thm_SZ_gVal_succ
import Theorems.Thm_SZ_eq_fixed_of_trapped
import Theorems.Thm_SZ_pick_eq_00
import Theorems.Thm_SZ_pick_eq_20
import Theorems.Thm_SZ_pick_snd_eq_two_iff

section
namespace SZ
open Filter Topology
private theorem t3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
private theorem t3_ub : Real.sqrt 3 < 1.8 := by
  have h : Real.sqrt 3 < Real.sqrt (1.8 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.8)] at h
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s : ℤ × ℤ} (h : GStart s) : ∃ k, (gDigit s k).2 = 2 := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ k, valS (gState s k) < 2 * Real.sqrt 3 := by
    intro k
    by_contra hx
    exact hcon k ((pick_snd_eq_two_iff _).mpr (not_lt.mp hx))
  have claim1 : ∀ k, valS (gState s k) ≤ 1 + Real.sqrt 3 →
      valS (gState s k) < 2 * Real.sqrt 3 / 3 := by
    intro k hle
    have hp : pick (valS (gState s k)) = (0, 0) := pick_eq_00 hle
    have hs : valS (gState s (k + 1)) = 3 * valS (gState s k) := by
      rw [gVal_succ, hp]; push_cast; ring
    have h2 := hlt (k + 1)
    rw [hs] at h2
    linarith
  have claim2 : ∀ k, 1 + Real.sqrt 3 < valS (gState s k) →
      valS (gState s k) < 2 + 2 * Real.sqrt 3 / 3 := by
    intro k hgt
    have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 hgt (hlt k)
    have hs : valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 := by
      rw [gVal_succ, hp]; push_cast; ring
    have h2 := hlt (k + 1)
    rw [hs] at h2
    linarith
  by_cases hex : ∃ j, 1 + Real.sqrt 3 < valS (gState s j)
  · obtain ⟨j, hj⟩ := hex
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < valS (gState s k) ∧
        valS (gState s k) < 2 + 2 * Real.sqrt 3 / 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj, claim2 j hj⟩
      | succ k hk ih =>
        have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 ih.1 (hlt k)
        have hs : valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 := by
          rw [gVal_succ, hp]; push_cast; ring
        have hgt : 1 + Real.sqrt 3 < valS (gState s (k + 1)) := by
          by_contra hle
          have h3 := claim1 (k + 1) (not_lt.mp hle)
          rw [hs] at h3
          linarith [t3_lb, ih.1]
        exact ⟨hgt, claim2 (k + 1) hgt⟩
    have hfix : valS (gState s j) = 6 / 2 := by
      refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6) (D := 1) (K := j)
        (fun k hk => ?_) (fun k hk => ?_)
      · show valS (gState s (k + 1)) = 3 * valS (gState s k) - 6
        have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 (habs k hk).1 (hlt k)
        rw [gVal_succ, hp]; push_cast; ring
      · show |valS (gState s k) - 6 / 2| ≤ 1
        obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]
        constructor <;> linarith [t3_lb, t3_ub]
    exact gVal_ne_three h j (by rw [hfix]; norm_num)
  · push Not at hex
    have htriple : ∀ n : ℕ, valS (gState s n) = 3 ^ n * valS (gState s 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hp : pick (valS (gState s n)) = (0, 0) := pick_eq_00 (hex n)
        rw [gVal_succ, hp]
        push_cast
        rw [ih, pow_succ]
        ring
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 + Real.sqrt 3) / valS (gState s 0))
      (by norm_num : (1:ℝ) < 3)
    have hb := hex n
    rw [htriple n] at hb
    have hlt2 := (div_lt_iff₀ (gVal_pos h 0)).mp hn
    linarith
end SZ
