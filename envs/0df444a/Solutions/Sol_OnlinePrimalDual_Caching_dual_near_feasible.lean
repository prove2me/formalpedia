-- Prove2me | solution 1 for OnlinePrimalDual.Caching.dual_near_feasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:55:19.887271+00:00
-- url     : https://prove2.me/submissions/dbd069b1-0a89-4466-9531-593c395dc9f8

import Mathlib
import Definitions.Def_OnlinePrimalDual_Caching_CachingInstance
import Definitions.Def_OnlinePrimalDual_Caching_dualSum
import Definitions.Def_OnlinePrimalDual_Caching_cachingX

namespace OnlinePrimalDual.Caching

theorem aux_dnf_core (D c k : ℝ) (hc : 1 ≤ c) (hk : 1 ≤ k)
    (h : c ≤ D → (1 / k) * Real.exp ((D - c) / c) ≤ 1) :
    D ≤ c * (1 + Real.log k) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk
  by_cases hD : c ≤ D
  · have h1 := h hD
    have h2 : Real.exp ((D - c) / c) ≤ k := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one hk0] at h1
      exact h1
    have h3 : (D - c) / c ≤ Real.log k := by
      rw [← Real.exp_le_exp, Real.exp_log hk0]
      exact h2
    rw [div_le_iff₀ hc0] at h3
    nlinarith
  · rw [not_le] at hD
    nlinarith

end OnlinePrimalDual.Caching

open OnlinePrimalDual.Caching

theorem solution {V Time : Type*} [Fintype V] [Fintype Time] [DecidableEq V]
    (inst : CachingInstance V Time) (y : Time → ℝ) (z : V → ℝ)
    (hy_nonneg : ∀ t, 0 ≤ y t) (hz_nonneg : ∀ v, 0 ≤ z v)
    (h_uncapped_le_one : ∀ v, inst.c v ≤ dualSum inst y v - z v →
      (1 / (inst.k : ℝ)) * Real.exp ((dualSum inst y v - z v - inst.c v) / inst.c v) ≤ 1) :
    ∀ v : V, dualSum inst y v - z v ≤ inst.c v * (1 + Real.log inst.k) := by
  intro v
  have hk : (1 : ℝ) ≤ (inst.k : ℝ) := by
    exact_mod_cast inst.hk_pos
  exact aux_dnf_core (dualSum inst y v - z v) (inst.c v) (inst.k : ℝ) (inst.hc_pos v) hk
    (h_uncapped_le_one v)
