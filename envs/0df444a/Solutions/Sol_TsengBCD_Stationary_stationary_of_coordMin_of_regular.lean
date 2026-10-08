-- Prove2me | solution 1 for TsengBCD.Stationary.stationary_of_coordMin_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T09:15:27.534549+00:00
-- url     : https://prove2.me/submissions/444a9448-4a20-4335-9945-126e1ab467e4

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting

open TsengBCD.Stationary Filter Topology

theorem solution {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (z : X n) :
    IsCoordMin f z → IsRegularAt f z → IsStationary f z := by
  intro hmin hreg
  refine ⟨hmin.1, fun d => hreg.2 d ?_⟩
  intro k
  unfold dirDeriv
  refine Filter.le_liminf_of_le (h := ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply EReal.mul_nonneg
  · apply (EReal.sub_nonneg (Or.inr hmin.1) (Or.inr (hbot z))).2
    have heq : t • (Pi.single k (d k) : X n) = (Pi.single k (t • d k) : X n) := by
      ext j
      by_cases hj : j = k
      · subst j
        simp
      · simp [Pi.single_eq_of_ne hj]
    rw [heq]
    exact hmin.2 k (t • d k)
  · exact_mod_cast (inv_nonneg.mpr (le_of_lt ht))

#print axioms solution
