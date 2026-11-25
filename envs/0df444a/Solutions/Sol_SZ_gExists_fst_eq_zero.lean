-- Prove2me | solution 1 for SZ.gExists_fst_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:49:26.875268+00:00
-- url     : https://prove2.me/submissions/8eda5fef-4ac2-4073-87c6-0f105c0dbe58

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_gVal_mem
import Theorems.Thm_SZ_gVal_ne_three
import Theorems.Thm_SZ_gVal_ne_top
import Theorems.Thm_SZ_gVal_succ
import Theorems.Thm_SZ_eq_fixed_of_trapped
import Theorems.Thm_SZ_pick_eq_20
import Theorems.Thm_SZ_pick_eq_22
import Theorems.Thm_SZ_pick_fst_eq_two_iff
import Theorems.Thm_SZ_pick_fst_mem

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
theorem _root_.solution {s : ℤ × ℤ} (h : GStart s) : ∃ k, (gDigit s k).1 = 0 := by
  by_contra hcon
  push Not at hcon
  have htwo : ∀ k, (pick (valS (gState s k))).1 = 2 := by
    intro k
    rcases pick_fst_mem (valS (gState s k)) with hx | hx
    · exact absurd hx (hcon k)
    · exact hx
  have hA : ∀ k, (1 + Real.sqrt 3 < valS (gState s k) ∧ valS (gState s k) < 2 * Real.sqrt 3)
      ∨ 1 + 3 * Real.sqrt 3 < valS (gState s k) := fun k =>
    (pick_fst_eq_two_iff _).mp (htwo k)
  by_cases hex : ∃ j, 1 + Real.sqrt 3 < valS (gState s j) ∧ valS (gState s j) < 2 * Real.sqrt 3
  · obtain ⟨j, hj1, hj2⟩ := hex
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < valS (gState s k) ∧
        valS (gState s k) < 2 * Real.sqrt 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj1, hj2⟩
      | succ k hk ih =>
        have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 ih.1 ih.2
        have hs : valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 := by
          rw [gVal_succ, hp]; push_cast; ring
        rcases hA (k + 1) with hx | hx
        · exact hx
        · exfalso; rw [hs] at hx; linarith [t3_lb, t3_ub, ih.2]
    have hfix : valS (gState s j) = 6 / 2 := by
      refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6) (D := 1) (K := j)
        (fun k hk => ?_) (fun k hk => ?_)
      · show valS (gState s (k + 1)) = 3 * valS (gState s k) - 6
        have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 (habs k hk).1 (habs k hk).2
        rw [gVal_succ, hp]; push_cast; ring
      · show |valS (gState s k) - 6 / 2| ≤ 1
        obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]
        constructor <;> linarith [t3_lb, t3_ub]
    exact gVal_ne_three h j (by rw [hfix]; norm_num)
  · push Not at hex
    have hA2 : ∀ k, 1 + 3 * Real.sqrt 3 < valS (gState s k) := by
      intro k
      rcases hA k with ⟨h1, h2⟩ | hx
      · exact absurd h2 (not_lt.mpr (hex k h1))
      · exact hx
    have hfix : valS (gState s 0) = (6 + 6 * Real.sqrt 3) / 2 := by
      refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6 + 6 * Real.sqrt 3)
        (D := 2) (K := 0) (fun k hk => ?_) (fun k hk => ?_)
      · show valS (gState s (k + 1)) = 3 * valS (gState s k) - (6 + 6 * Real.sqrt 3)
        have hp : pick (valS (gState s k)) = (2, 2) := pick_eq_22 (hA2 k)
        rw [gVal_succ, hp]; push_cast; ring
      · show |valS (gState s k) - (6 + 6 * Real.sqrt 3) / 2| ≤ 2
        have h1 := hA2 k
        have h2 := (gVal_mem h k).2
        rw [abs_le]
        constructor <;> linarith
    exact gVal_ne_top h 0 (by rw [hfix]; ring)
end SZ
