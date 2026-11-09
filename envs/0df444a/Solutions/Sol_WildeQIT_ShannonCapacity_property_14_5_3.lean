-- Prove2me | solution 1 for WildeQIT.ShannonCapacity.property_14_5_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:13:48.862787+00:00
-- url     : https://prove2.me/submissions/a5e039fa-b0ff-4d33-a56c-8abf97eb6adf

import Definitions.Def_WildeQIT_jointTypicalSet
import Definitions.Def_WildeQIT_jointEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open WildeQIT in
theorem solution {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : FinDist (α × β)) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (z : Fin n → α × β)
    (hz : z ∈ jointTypicalSet p n δ) :
    (2 : ℝ) ^ (-((n : ℝ) * (jointEntropy p + δ))) ≤ (p.iid n).prob z ∧
      (p.iid n).prob z ≤ (2 : ℝ) ^ (-((n : ℝ) * (jointEntropy p - δ))) := by
  obtain ⟨hP, hS, -, -⟩ := mem_jointTypicalSet.mp hz
  unfold jointEntropy
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [FinDist.iid_prob]
  · have hnr : (0:ℝ) < n := by exact_mod_cast hn
    unfold sampleEntropy at hS
    rw [abs_le] at hS
    obtain ⟨h1, h2⟩ := hS
    set L := Real.logb 2 ((p.iid n).prob z) with hL
    have e : (n:ℝ) * (-(1 / (n:ℝ)) * L) = -L := by
      have := hnr.ne'
      field_simp
    have hL1 : -((n:ℝ) * (entropy p + δ)) ≤ L := by
      have := mul_le_mul_of_nonneg_left h2 hnr.le
      rw [mul_sub, e] at this
      nlinarith
    have hL2 : L ≤ -((n:ℝ) * (entropy p - δ)) := by
      have := mul_le_mul_of_nonneg_left h1 hnr.le
      rw [mul_sub, e] at this
      nlinarith
    have hrp : (2:ℝ) ^ L = (p.iid n).prob z := Real.rpow_logb (by norm_num) (by norm_num) hP
    constructor
    · rw [← hrp]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hL1
    · rw [← hrp]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hL2
