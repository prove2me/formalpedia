-- Prove2me | solution 1 for PBElicit.RandThresh.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:48:22.444422+00:00
-- url     : https://prove2.me/submissions/82213f71-665b-4667-9b12-1c1fa7950077

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting
import Theorems.Thm_PBElicit_RandThresh_eq_6

open Classical PBElicit.RandThresh

theorem solution {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (v : Fin n → A → ℝ) (hv : IsUtilityProfile v) (m K : ℕ) (hA : Fintype.card A = m)
    (hmK : m = 2 ^ K) (Sstar : Finset A) (hS : IsWelfareOptimal c v Sstar)
    (k : ℕ) (hk : k ≤ 2 * K) :
    ∑ j ∈ Finset.Icc 1 (2 * K), (cntStar v c m Sstar j k : ℝ) * lo m j
        ≤ sw v (Sstar ∩ bucket c m k) ∧
      sw v (Sstar ∩ bucket c m k)
        ≤ ((Sstar ∩ bucket c m k).card : ℝ) * ((n : ℝ) / (m : ℝ) ^ 2)
          + ∑ j ∈ Finset.Icc 1 (2 * K), (cntStar v c m Sstar j k : ℝ) * up m j := by
  have key := fun a => eq_6 v hv m K hA hmK a
  unfold cntStar sw
  push_cast
  simp only [Finset.sum_mul]
  constructor
  · rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun a _ => (key a).1)
  · rw [Finset.sum_comm (s := Finset.Icc 1 (2 * K))]
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun a _ => (key a).2)
