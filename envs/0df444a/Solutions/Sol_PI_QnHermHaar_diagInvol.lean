-- Prove2me | solution 1 for PI.QnHermHaar.diagInvol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:16:26.674125+00:00
-- url     : https://prove2.me/submissions/6a4ebe42-2b6f-4d15-9f9c-fb7406301ffd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {m : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) (hH : Hmᴴ = Hm) (h2 : Hm * Hm = 1) :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ), star U * U = 1 ∧ U * star U = 1 ∧
      Hm * U = U * diagonal (fun j => ((ε j : ℤ) : ℂ)) := by
  have hA : Hm.IsHermitian := hH
  have hu1 : star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hu2 : (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  set lam : Fin m → ℂ := fun j => ((hA.eigenvalues j : ℝ) : ℂ) with hlam
  have hHU : Hm * U = U * diagonal lam := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    have h := congrFun (hA.mulVec_eigenvectorBasis j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at h
    simp only [hU, Matrix.IsHermitian.eigenvectorUnitary_apply, hlam]
    rw [h, mul_comm]
  have hD1 : star U * Hm * U = diagonal lam := by
    rw [Matrix.mul_assoc, hHU, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hD : diagonal lam * diagonal lam = 1 := by
    rw [← hD1]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U (star U), hu2, Matrix.one_mul, ← Matrix.mul_assoc Hm Hm, h2, Matrix.one_mul, hu1]
  have hr : ∀ j, hA.eigenvalues j = 1 ∨ hA.eigenvalues j = -1 := by
    intro j
    have h := congrFun (congrFun hD j) j
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
    simp only [hlam] at h
    have h' : hA.eigenvalues j * hA.eigenvalues j = 1 := by exact_mod_cast h
    exact mul_self_eq_one_iff.mp h'
  refine ⟨U, fun j => if hA.eigenvalues j = 1 then 1 else -1, hu1, hu2, ?_⟩
  rw [hHU]
  congr 2
  funext j
  rcases hr j with h | h
  · simp [hlam, h]
  · have hn : ¬ hA.eigenvalues j = 1 := by rw [h]; norm_num
    show ((hA.eigenvalues j : ℝ) : ℂ) = (((if hA.eigenvalues j = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) : ℂ)
    rw [if_neg hn, h]
    simp
end PI.QnHermHaar
