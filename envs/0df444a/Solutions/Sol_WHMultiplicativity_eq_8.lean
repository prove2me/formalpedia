-- Prove2me | solution 1 for WHMultiplicativity.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:16:37.80474+00:00
-- url     : https://prove2.me/submissions/e6e31709-5563-46f9-808c-0bba77bc929f

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi

theorem solution (d : ℕ) (hd : 2 ≤ d) (φ : Fin d → ℂ) (hφ : IsUnitVector φ) :
    wernerHolevo d (pureState φ) = ((d : ℂ) - 1)⁻¹ • (1 - pureState (star φ)) := by
  unfold wernerHolevo pureState
  have htr : (Matrix.vecMulVec φ (star φ)).trace = 1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply]
    calc ∑ i, φ i * star (φ i) = ∑ i, ((Complex.normSq (φ i) : ℝ) : ℂ) :=
          Finset.sum_congr rfl (fun i _ => Complex.mul_conj (φ i))
      _ = ((∑ i, Complex.normSq (φ i) : ℝ) : ℂ) := by push_cast; rfl
      _ = 1 := by rw [hφ]; simp
  rw [htr, one_smul]
  congr 2
  ext i j
  simp [Matrix.vecMulVec_apply, mul_comm]
