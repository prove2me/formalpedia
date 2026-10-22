-- Prove2me | solution 1 for StatComplexityDM.Estimation.affinity_eq_one_sub_half_hellinger
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:46:03.023556+00:00
-- url     : https://prove2.me/submissions/3b321e6a-77eb-4665-906d-7b15866cd2ec

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_StatComplexityDM_Estimation_Sequential

set_option autoImplicit false

open FoundationsRL.GeneralDM Classical

theorem solution {Y : Type*} [Fintype Y]
    (P Q : Y → ℝ) (hP : StatComplexityDM.LowerBound.IsDist P) (hQ : StatComplexityDM.LowerBound.IsDist Q) :
    (∑ y, Real.sqrt (P y * Q y)) = 1 - hellingerSq P Q / 2 ∧
    (∑ y, if 0 < P y then P y * Real.sqrt (Q y / P y) else 0) =
      1 - hellingerSq P Q / 2 := by
  have key : ∀ y, Real.sqrt (P y * Q y) = Real.sqrt (P y) * Real.sqrt (Q y) :=
    fun y => Real.sqrt_mul (hP.1 y) _
  have h1 : hellingerSq P Q = 2 - 2 * ∑ y, Real.sqrt (P y * Q y) := by
    unfold hellingerSq
    have : ∀ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2 = P y + Q y - 2 * Real.sqrt (P y * Q y) := by
      intro y
      rw [key, sub_sq, Real.sq_sqrt (hP.1 y), Real.sq_sqrt (hQ.1 y)]
      ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hP.2, hQ.2, ← Finset.mul_sum]
    ring
  have h2 : ∀ y, (if 0 < P y then P y * Real.sqrt (Q y / P y) else 0) = Real.sqrt (P y * Q y) := by
    intro y
    split_ifs with h
    · rw [Real.sqrt_div (hQ.1 y), key]
      have hs : 0 < Real.sqrt (P y) := Real.sqrt_pos.2 h
      calc P y * (Real.sqrt (Q y) / Real.sqrt (P y))
          = (Real.sqrt (P y)) ^ 2 * (Real.sqrt (Q y) / Real.sqrt (P y)) := by
            rw [Real.sq_sqrt (hP.1 y)]
        _ = Real.sqrt (P y) * Real.sqrt (Q y) := by field_simp
    · have h0 : P y = 0 := le_antisymm (not_lt.1 h) (hP.1 y)
      rw [h0]; simp
  refine ⟨by rw [h1]; ring, ?_⟩
  simp_rw [h2]
  rw [h1]; ring
