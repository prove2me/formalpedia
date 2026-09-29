-- Prove2me | solution 1 for OnlinePrimalDual.Caching.algorithm_competitive_ratio
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:00:09.939948+00:00
-- url     : https://prove2.me/submissions/07253535-1417-47ad-ae6b-dcc81daa0f03

import Mathlib
import Definitions.Def_OnlinePrimalDual_Caching_CachingInstance
import Definitions.Def_OnlinePrimalDual_Caching_dualSum
import Definitions.Def_OnlinePrimalDual_Caching_cachingX
import Definitions.Def_OnlinePrimalDual_Caching_DualObjective

namespace OnlinePrimalDual.Caching

theorem aux_ocr_swap {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (w : V → ℝ) :
    ∑ v, w v * dualSum inst y v = ∑ t, y t * ∑ v ∈ inst.S t, w v := by
  unfold dualSum
  simp only [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

theorem aux_ocr_nonneg {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (z : V → ℝ) (v : V) :
    0 ≤ cachingX inst y z v := by
  unfold cachingX
  split_ifs with h
  · exact le_refl 0
  · refine le_min zero_le_one ?_
    have hk : (0 : ℝ) < inst.k := by exact_mod_cast inst.hk_pos
    positivity

theorem aux_ocr_act {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (z : V → ℝ) (v : V) :
    inst.c v * cachingX inst y z v ≤ cachingX inst y z v * (dualSum inst y v - z v) := by
  have h0 := aux_ocr_nonneg inst y z v
  by_cases h : dualSum inst y v - z v < inst.c v
  · have : cachingX inst y z v = 0 := by unfold cachingX; rw [if_pos h]
    rw [this]; simp
  · push Not at h
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left h h0

end OnlinePrimalDual.Caching

open OnlinePrimalDual.Caching

theorem solution {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (z : V → ℝ)
    (hy_nonneg : ∀ t, 0 ≤ y t) (hz_nonneg : ∀ v, 0 ≤ z v)
    (h_feasible : ∀ t, inst.rhs t ≤ ∑ v ∈ inst.S t, cachingX inst y z v)
    (h_comp_slack : ∀ t, 0 < y t → inst.rhs t = ∑ v ∈ inst.S t, cachingX inst y z v)
    (h_comp_slack_z : ∀ v, 0 < z v → cachingX inst y z v = 1)
    (h_dual_near_feasible : ∀ v : V, dualSum inst y v - z v ≤ inst.c v * (1 + Real.log inst.k)) :
    ∀ x'' : V → ℝ, (∀ v, 0 ≤ x'' v) → (∀ v, x'' v ≤ 1) →
      (∀ t, inst.rhs t ≤ ∑ v ∈ inst.S t, x'' v) →
      ∑ v, inst.c v * cachingX inst y z v ≤
        2 * (1 + Real.log inst.k) * ∑ v, inst.c v * x'' v := by
  intro x'' hx0 hx1 hxf
  set x := cachingX inst y z with hxdef
  set L : ℝ := 1 + Real.log inst.k with hL
  have hk1 : (1 : ℝ) ≤ inst.k := by exact_mod_cast inst.hk_pos
  have hLge : 1 ≤ L := by
    have := Real.log_nonneg hk1
    linarith
  -- Step 1: primal cost ≤ dual objective
  have h1 : ∑ v, inst.c v * x v ≤ ∑ v, x v * (dualSum inst y v - z v) :=
    Finset.sum_le_sum (fun v _ => aux_ocr_act inst y z v)
  have h2 : ∑ v, x v * (dualSum inst y v - z v) =
      ∑ v, x v * dualSum inst y v - ∑ v, x v * z v := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    ring
  have h3 : ∑ v, x v * z v = ∑ v, z v := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rcases (hz_nonneg v).lt_or_eq with h | h
    · rw [h_comp_slack_z v h]; ring
    · rw [← h]; ring
  have h4 : ∑ v, x v * dualSum inst y v = ∑ t, inst.rhs t * y t := by
    rw [aux_ocr_swap]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rcases (hy_nonneg t).lt_or_eq with h | h
    · rw [h_comp_slack t h]; ring
    · rw [← h]; ring
  -- Step 2: dual objective ≤ L * cost of x''
  have h5 : ∑ t, inst.rhs t * y t ≤ ∑ v, x'' v * dualSum inst y v := by
    rw [aux_ocr_swap]
    refine Finset.sum_le_sum (fun t _ => ?_)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hxf t) (hy_nonneg t)
  have h6 : ∑ v, x'' v * z v ≤ ∑ v, z v :=
    Finset.sum_le_sum (fun v _ => by
      have := mul_le_mul_of_nonneg_right (hx1 v) (hz_nonneg v)
      linarith)
  have h7 : ∑ v, x'' v * dualSum inst y v - ∑ v, x'' v * z v ≤ L * ∑ v, inst.c v * x'' v := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum (fun v _ => ?_)
    have := mul_le_mul_of_nonneg_left (h_dual_near_feasible v) (hx0 v)
    nlinarith
  have hS : 0 ≤ ∑ v, inst.c v * x'' v :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (by linarith [inst.hc_pos v]) (hx0 v))
  have h8 : L * ∑ v, inst.c v * x'' v ≤ 2 * L * ∑ v, inst.c v * x'' v := by
    nlinarith
  linarith
