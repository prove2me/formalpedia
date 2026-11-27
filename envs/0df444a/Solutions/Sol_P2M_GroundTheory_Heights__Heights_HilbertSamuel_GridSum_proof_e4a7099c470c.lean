-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_proof_e4a7099c470c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:30.885982+00:00
-- url     : https://prove2.me/submissions/ec134f07-bab8-486a-ae74-cf6996525b33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGridSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_range_8f1b7a26fca2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_choose_le_pow_div_factorial_e7e62f8ad023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_div_factorial_le_acf8885772b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GridSum_pow_sub_pow_le_0e7651b435b6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Finset Filter Asymptotics
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace GridSum
theorem _root_.solution : GridSum.Statement := by
  intro D i hi
  set j := D - i with hj
  have hD : i + j + 1 = D + 1 := by omega
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF1 : (1 : ℝ) ≤ F := by
    rw [hFdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF : 0 < F := lt_of_lt_of_le one_pos hF1
  have lower : ∀ n : ℕ, ((n.choose (D + 1) : ℕ) : ℝ) ≤ ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) := by
    intro n
    have h := GridSum.choose_range n i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    apply sum_le_sum
    intro a _
    rw [mul_div_mul_comm, Nat.cast_mul]
    exact mul_le_mul (GridSum.choose_le_pow_div_factorial _ _)
      (GridSum.choose_le_pow_div_factorial _ _) (by positivity) (by positivity)
  have upper : ∀ n : ℕ, ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) ≤
        (((n + D).choose (D + 1) : ℕ) : ℝ) := by
    intro n
    have h := GridSum.choose_range (n + D) i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    calc ∑ a ∈ range n,
          (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ))
        ≤ ∑ a ∈ range n, (((a + i).choose i * (n + D - 1 - (a + i)).choose j : ℕ) : ℝ) := by
          apply sum_le_sum
          intro a ha
          have hb : n + D - 1 - (a + i) = (n - 1 - a) + j := by
            have := mem_range.mp ha; omega
          rw [hb, mul_div_mul_comm, Nat.cast_mul]
          exact mul_le_mul (GridSum.pow_div_factorial_le _ _)
            (GridSum.pow_div_factorial_le _ _) (by positivity) (by positivity)
      _ = ∑ a ∈ (range n).map (addRightEmbedding i),
            ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          rw [sum_map]; rfl
      _ ≤ ∑ a ∈ range (n + D), ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_map] at hx
            obtain ⟨a, ha, rfl⟩ := hx
            rw [mem_range] at ha ⊢
            change a + i < n + D
            omega
          · intros; positivity
  refine IsBigO.of_bound (((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D) ?_
  filter_upwards [eventually_ge_atTop D] with n hn
  have hL := lower n
  have hU := upper n
  set S := ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) with hS
  have hnD : (D : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - D) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
    have h : (n - D) ^ (D + 1) ≤ n.choose (D + 1) * (D + 1).factorial := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      have := Nat.pow_sub_le_descFactorial n (D + 1)
      rwa [show n + 1 - (D + 1) = n - D by omega] at this
    have h' : (((n - D : ℕ) : ℝ)) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
      rw [hFdef]; exact_mod_cast h
    rwa [Nat.cast_sub hn] at h'
  have h2 : (((n + D).choose (D + 1) : ℕ) : ℝ) * F ≤ ((n : ℝ) + D) ^ (D + 1) := by
    have h : (n + D).choose (D + 1) * (D + 1).factorial ≤ (n + D) ^ (D + 1) := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow _ _
    rw [hFdef]; exact_mod_cast h
  have hSlo : ((n : ℝ) - D) ^ (D + 1) / F ≤ S := by
    rw [div_le_iff₀ hF]; nlinarith
  have hShi : S ≤ ((n : ℝ) + D) ^ (D + 1) / F := by
    rw [le_div_iff₀ hF]; nlinarith
  have hy : (0 : ℝ) ≤ (n : ℝ) - D := sub_nonneg.mpr hnD
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hp1 : ((n : ℝ) - D) ^ (D + 1) ≤ (n : ℝ) ^ (D + 1) :=
    pow_le_pow_left₀ hy (by linarith) _
  have hp2 : (n : ℝ) ^ (D + 1) ≤ ((n : ℝ) + D) ^ (D + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _
  have hgap := GridSum.pow_sub_pow_le ((n : ℝ) + D) ((n : ℝ) - D) (D + 1) hy (by linarith)
  rw [Nat.add_sub_cancel] at hgap
  have hpow : ((n : ℝ) + D) ^ D ≤ 2 ^ D * (n : ℝ) ^ D := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have habs : |S - (n : ℝ) ^ (D + 1) / F| ≤
      ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F := by
    rw [abs_le, sub_div]
    constructor
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
  have hnum : 0 ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := by linarith
  have hdiv : ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F ≤
      ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := div_le_self hnum hF1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)]
  have hk : (0 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) := by positivity
  calc |S - (n : ℝ) ^ (D + 1) / F|
      ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := habs.trans hdiv
    _ ≤ ((D + 1 : ℕ) : ℝ) * ((n + D) - (n - D)) * ((n : ℝ) + D) ^ D := hgap
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * ((n : ℝ) + D) ^ D := by ring
    _ ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) * (2 ^ D * (n : ℝ) ^ D) := mul_le_mul_of_nonneg_left hpow hk
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D * (n : ℝ) ^ D := by ring
end GridSum
end GroundTheory.Heights₂.Heights.HilbertSamuel
