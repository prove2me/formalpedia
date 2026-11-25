-- Prove2me | solution 1 for SZ.gExists_inO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:30.518353+00:00
-- url     : https://prove2.me/submissions/85627935-f86e-4460-9434-fb78bec52e65

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_gVal_mem
import Theorems.Thm_SZ_gVal_pos
import Theorems.Thm_SZ_gVal_ne_three
import Theorems.Thm_SZ_gVal_ne_top
import Theorems.Thm_SZ_gVal_ne_threeRoot
import Theorems.Thm_SZ_gVal_succ
import Theorems.Thm_SZ_pick_eq_02
import Theorems.Thm_SZ_zones_of_not_InO
import Theorems.Thm_SZ_eq_fixed_of_trapped
import Theorems.Thm_SZ_pick_eq_00
import Theorems.Thm_SZ_pick_eq_20
import Theorems.Thm_SZ_pick_eq_22

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
theorem _root_.solution {s : ℤ × ℤ} (h : GStart s) : ∃ k, InO (valS (gState s k)) := by
  by_contra hcon
  push Not at hcon
  have hz : ∀ k, valS (gState s k) < 2 ∨
      (1 + Real.sqrt 3 < valS (gState s k) ∧ valS (gState s k) < 2 * Real.sqrt 3) ∨
      (3 + Real.sqrt 3 < valS (gState s k) ∧ valS (gState s k) < 2 + 2 * Real.sqrt 3) ∨
      1 + 3 * Real.sqrt 3 < valS (gState s k) := fun k =>
    zones_of_not_InO (hcon k)
  -- the four forced steps
  have step1 : ∀ k, valS (gState s k) < 2 →
      valS (gState s (k + 1)) = 3 * valS (gState s k) := by
    intro k hk
    have hp : pick (valS (gState s k)) = (0, 0) := pick_eq_00 (by linarith [t3_lb])
    rw [gVal_succ, hp]; push_cast; ring
  have step2 : ∀ k, 1 + Real.sqrt 3 < valS (gState s k) → valS (gState s k) < 2 * Real.sqrt 3 →
      valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 := by
    intro k h1 h2
    have hp : pick (valS (gState s k)) = (2, 0) := pick_eq_20 h1 h2
    rw [gVal_succ, hp]; push_cast; ring
  have step3 : ∀ k, 3 + Real.sqrt 3 < valS (gState s k) →
      valS (gState s k) < 2 + 2 * Real.sqrt 3 →
      valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 * Real.sqrt 3 := by
    intro k h1 h2
    have hp : pick (valS (gState s k)) = (0, 2) :=
      pick_eq_02 (by linarith [t3_lb, t3_ub]) (by linarith [t3_lb])
    rw [gVal_succ, hp]; push_cast; ring
  have step4 : ∀ k, 1 + 3 * Real.sqrt 3 < valS (gState s k) →
      valS (gState s (k + 1)) = 3 * valS (gState s k) - (6 + 6 * Real.sqrt 3) := by
    intro k hk
    have hp : pick (valS (gState s k)) = (2, 2) := pick_eq_22 hk
    rw [gVal_succ, hp]; push_cast; ring
  -- Z₂ is absorbing
  by_cases hZ2 : ∃ j, 1 + Real.sqrt 3 < valS (gState s j) ∧ valS (gState s j) < 2 * Real.sqrt 3
  · obtain ⟨j, hj1, hj2⟩ := hZ2
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < valS (gState s k) ∧
        valS (gState s k) < 2 * Real.sqrt 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj1, hj2⟩
      | succ k hk ih =>
        have hs := step2 k ih.1 ih.2
        rcases hz (k + 1) with hx | hx | hx | hx <;> rw [hs] at hx ⊢
        · exact absurd hx (by push Not; linarith [t3_lb, ih.1])
        · exact hx
        · exact absurd hx.1 (by push Not; linarith [t3_ub, ih.2])
        · exact absurd hx (by push Not; linarith [t3_ub, ih.2])
    have hfix : valS (gState s j) = 6 / 2 := by
      refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6) (D := 1) (K := j)
        (fun k hk => ?_) (fun k hk => ?_)
      · show valS (gState s (k + 1)) = 3 * valS (gState s k) - 6
        exact step2 k (habs k hk).1 (habs k hk).2
      · show |valS (gState s k) - 6 / 2| ≤ 1
        obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]; constructor <;> linarith [t3_lb, t3_ub]
    exact gVal_ne_three h j (by rw [hfix]; norm_num)
  -- Z₃ is absorbing
  · push Not at hZ2
    by_cases hZ3 : ∃ j, 3 + Real.sqrt 3 < valS (gState s j) ∧
        valS (gState s j) < 2 + 2 * Real.sqrt 3
    · obtain ⟨j, hj1, hj2⟩ := hZ3
      have habs : ∀ k, j ≤ k → 3 + Real.sqrt 3 < valS (gState s k) ∧
          valS (gState s k) < 2 + 2 * Real.sqrt 3 := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => exact ⟨hj1, hj2⟩
        | succ k hk ih =>
          have hs := step3 k ih.1 ih.2
          rcases hz (k + 1) with hx | hx | hx | hx <;> rw [hs] at hx ⊢
          · exact absurd hx (by push Not; linarith [t3_ub, ih.1])
          · exact absurd hx.2 (by push Not; linarith [t3_ub, ih.1])
          · exact hx
          · exact absurd hx (by push Not; linarith [t3_lb, ih.2])
      have hfix : valS (gState s j) = 6 * Real.sqrt 3 / 2 := by
        refine eq_fixed_of_trapped (f := fun k => valS (gState s k)) (c := 6 * Real.sqrt 3)
          (D := 1) (K := j) (fun k hk => ?_) (fun k hk => ?_)
        · show valS (gState s (k + 1)) = 3 * valS (gState s k) - 6 * Real.sqrt 3
          exact step3 k (habs k hk).1 (habs k hk).2
        · show |valS (gState s k) - 6 * Real.sqrt 3 / 2| ≤ 1
          obtain ⟨ha, hb⟩ := habs k hk
          rw [abs_le]; constructor <;> linarith [t3_lb, t3_ub]
      exact gVal_ne_threeRoot h j (by rw [hfix]; ring)
    -- only Z₁ and Z₄ remain, and neither leads to the other
    · push Not at hZ3
      have hz14 : ∀ k, valS (gState s k) < 2 ∨ 1 + 3 * Real.sqrt 3 < valS (gState s k) := by
        intro k
        rcases hz k with hx | hx | hx | hx
        · exact Or.inl hx
        · exact absurd hx.2 (not_lt.mpr (hZ2 k hx.1))
        · exact absurd hx.2 (not_lt.mpr (hZ3 k hx.1))
        · exact Or.inr hx
      by_cases hZ4 : ∃ j, 1 + 3 * Real.sqrt 3 < valS (gState s j)
      · obtain ⟨j, hj⟩ := hZ4
        have habs : ∀ k, j ≤ k → 1 + 3 * Real.sqrt 3 < valS (gState s k) := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => exact hj
          | succ k hk ih =>
            have hs := step4 k ih
            rcases hz14 (k + 1) with hx | hx
            · exfalso; rw [hs] at hx; linarith [t3_lb]
            · exact hx
        have hfix : valS (gState s j) = (6 + 6 * Real.sqrt 3) / 2 := by
          refine eq_fixed_of_trapped (f := fun k => valS (gState s k))
            (c := 6 + 6 * Real.sqrt 3) (D := 2) (K := j) (fun k hk => ?_) (fun k hk => ?_)
          · show valS (gState s (k + 1)) = 3 * valS (gState s k) - (6 + 6 * Real.sqrt 3)
            exact step4 k (habs k hk)
          · show |valS (gState s k) - (6 + 6 * Real.sqrt 3) / 2| ≤ 2
            have h1 := habs k hk
            have h2 := (gVal_mem h k).2
            rw [abs_le]; constructor <;> linarith
        exact gVal_ne_top h j (by rw [hfix]; ring)
      · push Not at hZ4
        have hone : ∀ k, valS (gState s k) < 2 := by
          intro k
          rcases hz14 k with hx | hx
          · exact hx
          · exact absurd hx (not_lt.mpr (hZ4 k))
        have htriple : ∀ n : ℕ, valS (gState s n) = 3 ^ n * valS (gState s 0) := by
          intro n
          induction n with
          | zero => simp
          | succ n ih => rw [step1 n (hone n), ih, pow_succ]; ring
        obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / valS (gState s 0))
          (by norm_num : (1:ℝ) < 3)
        have hb := hone n
        rw [htriple n] at hb
        have hlt2 := (div_lt_iff₀ (gVal_pos h 0)).mp hn
        linarith
end SZ
