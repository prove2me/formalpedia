-- Prove2me | solution 1 for SeqDiagnosis.BeliefRecon.row_RP_eq_beta
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:57:31.05774+00:00
-- url     : https://prove2.me/submissions/e5bc996f-2e85-457b-a5fa-dec78ef585a5

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Model

open Matrix SeqDiagnosis.BeliefRecon

theorem solution {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (hRP : M.Bmat = R * P) (j : Fin N) :
    (R * P) j = M.beta j ∧
    betaZero M R P j = M.normConst (M.beta j) ∧
    ∀ ys : List Y, ys ≠ [] →
      (ys.length : ℝ) * (betaZero M R P j + (R *ᵥ diagStat M P ys) j) =
        (ys.length : ℝ) * M.normConst (M.beta j) + M.beta j ⬝ᵥ (ys.map M.h).sum := by
  have h1 : (R * P) j = M.beta j := by rw [← hRP]; rfl
  have h2 : betaZero M R P j = M.normConst (M.beta j) := by
    simp only [betaZero, h1]
  refine ⟨h1, h2, ?_⟩
  intro ys hys
  have hlen : (ys.length : ℝ) ≠ 0 := by
    have : ys.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hys
    exact_mod_cast this
  have h3 : (R *ᵥ diagStat M P ys) j = (ys.length : ℝ)⁻¹ * (M.beta j ⬝ᵥ (ys.map M.h).sum) := by
    simp only [diagStat, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [← h1]
    rfl
  rw [h2, h3, mul_add, ← mul_assoc, mul_inv_cancel₀ hlen, one_mul]
