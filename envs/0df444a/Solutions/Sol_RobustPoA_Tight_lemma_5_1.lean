-- Prove2me | solution 1 for RobustPoA.Tight.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-15T21:21:33.154711+00:00
-- url     : https://prove2.me/submissions/9b82693e-c275-4eb7-94df-05f3428a7282

import Definitions.Def_RobustPoA_Tight_Classes
import Mathlib

set_option autoImplicit false

open RobustPoA.Tight

theorem solution (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c ∧ IsStrictlyPos c)
    (p : ℝ × ℝ) (hp : p ∈ smoothParams C) : 0 ≤ p.2 := by
  by_contra hcon
  have hp2neg : p.2 < 0 := not_le.mp hcon
  have hp' : p.2 < 1 ∧ ∀ c ∈ C, ∀ x x' : ℕ, 1 ≤ x' →
      c (x + 1) * (x' : ℝ) ≤ p.1 * (c x' * (x' : ℝ)) + p.2 * (c x * (x : ℝ)) := hp
  obtain ⟨hp2lt1, hsm⟩ := hp'
  obtain ⟨c, hcC⟩ := hne
  obtain ⟨hCost, hPos⟩ := hC c hcC
  have hCost' : (∀ x, 1 ≤ x → 0 ≤ c x) ∧ (∀ x y, 1 ≤ x → x ≤ y → c x ≤ c y) ∧
      ∃ x, 1 ≤ x ∧ c x ≠ 0 := hCost
  obtain ⟨hCostNonneg, hCostMono, hCostNe⟩ := hCost'
  have hPos' : ∀ x, 1 ≤ x → 0 < c x := hPos
  have hc1 : 0 < c 1 := hPos' 1 le_rfl
  obtain ⟨N, hN⟩ := exists_nat_gt ((p.1 - 1) / (-p.2))
  -- Instantiate the resourcewise constraint at (x, x') = (N + 1, 1).
  have hsm_inst := hsm c hcC (N + 1) 1 (by omega)
  simp only [Nat.cast_one, mul_one] at hsm_inst
  have hmono_x : c 1 ≤ c (N + 1) := hCostMono 1 (N + 1) le_rfl (by omega)
  have hmono_x1 : c 1 ≤ c (N + 1 + 1) := hCostMono 1 (N + 1 + 1) le_rfl (by omega)
  have hcast : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmul : c 1 * ((N + 1 : ℕ) : ℝ) ≤ c (N + 1) * ((N + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hmono_x hcast
  -- Since p.2 < 0, multiplying by p.2 flips the inequality.
  have hmul2 : p.2 * (c (N + 1) * ((N + 1 : ℕ) : ℝ)) ≤
      p.2 * (c 1 * ((N + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonpos_left hmul hp2neg.le
  have hneg : 0 < -p.2 := neg_pos.mpr hp2neg
  have hN' : p.1 - 1 < (N : ℝ) * (-p.2) := (div_lt_iff₀ hneg).mp hN
  -- The Archimedean choice of N forces p.1 + p.2 * (N + 1) < 1.
  have hchoice : p.1 + p.2 * ((N + 1 : ℕ) : ℝ) < 1 := by
    have hcastN1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hcastN1]
    have hN'' : p.2 * (N : ℝ) < 1 - p.1 := by
      have hrr : (N : ℝ) * (-p.2) = -(p.2 * (N : ℝ)) := by ring
      linarith [hN']
    have hsplit : p.2 * ((N : ℝ) + 1) = p.2 * (N : ℝ) + p.2 := by ring
    rw [hsplit]
    linarith [hN'']
  -- Chain: c 1 ≤ c (N+2) ≤ p.1 * c 1 + p.2 * (c (N+1) * (N+1))
  --        ≤ p.1 * c 1 + p.2 * (c 1 * (N+1)) = c 1 * (p.1 + p.2 * (N+1)).
  have hle : c 1 ≤ c 1 * (p.1 + p.2 * ((N + 1 : ℕ) : ℝ)) := by
    have hrw : c 1 * (p.1 + p.2 * ((N + 1 : ℕ) : ℝ)) =
        p.1 * c 1 + p.2 * (c 1 * ((N + 1 : ℕ) : ℝ)) := by ring
    rw [hrw]
    linarith [hmono_x1, hsm_inst, hmul2]
  -- Divide by c 1 > 0 and contradict the Archimedean choice.
  have hle1 : (1 : ℝ) ≤ p.1 + p.2 * ((N + 1 : ℕ) : ℝ) :=
    le_of_mul_le_mul_left (by rw [mul_one]; exact hle) hc1
  linarith [hle1, hchoice]

theorem RobustPoA.Tight.lemma_5_1 (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c ∧ IsStrictlyPos c)
    (p : ℝ × ℝ) (hp : p ∈ smoothParams C) : 0 ≤ p.2 := solution C hne hC p hp
