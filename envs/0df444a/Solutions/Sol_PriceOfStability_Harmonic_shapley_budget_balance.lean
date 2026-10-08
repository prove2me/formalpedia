-- Prove2me | solution 1 for PriceOfStability.Harmonic.shapley_budget_balance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:03:22.895562+00:00
-- url     : https://prove2.me/submissions/49bd9bed-12a9-4adb-8b1e-6d49865bc54a

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

set_option autoImplicit false

open CongestionPoA.AsymSum

open CongestionPoA.AsymSum PriceOfStability.Harmonic in
theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ) (S : ι → Finset E) :
    sumCost (fairGame strategies c) S = designCost c S := by
  unfold sumCost cost designCost fairGame
  simp only
  rw [Finset.sum_filter]
  have h : ∀ i, ∑ e ∈ S i, c e (load S e) / (load S e : ℝ)
      = ∑ e, if e ∈ S i then c e (load S e) / (load S e : ℝ) else 0 := fun i => by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hl : ((Finset.univ.filter (fun i => e ∈ S i)).card : ℝ) = (load S e : ℝ) := rfl
  rw [hl]
  split_ifs with hpos
  · have : (load S e : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
  · have : load S e = 0 := by omega
    simp [this]
