-- Prove2me | solution 1 for PI.IsoDerivBFintype.minor_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:45.240302+00:00
-- url     : https://prove2.me/submissions/5c9047cd-a59e-4b70-ab43-ac4573ab6b96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_IsoDerivB
import Theorems.Thm_PI_IsoDerivBFintype_cauchyBinet
import Theorems.Thm_PI_IsoDerivBFintype_le_of_oe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
variable {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)
namespace PI.IsoDerivBFintype
theorem _root_.solution (τ : T) {h : ℕ} (Jc : Fin h ↪o Fin N) :
    MvPolynomial.aeval (gD s y') (Matrix.det (Matrix.of fun i j : Fin h =>
      if hj : (j : ℕ) < N then (MvPolynomial.X (τ, Jc i, ⟨j, hj⟩) : MvPolynomial (FrV T N) ℂ)
      else 0))
    = ∑ I : Fin h ↪o Fin N', Matrix.det (Matrix.of fun i k : Fin h =>
        MvPolynomial.C (s τ) *
          (MvPolynomial.X ((τ, I i, Jc k) : Idx T N N') : MvPolynomial (Idx T N N') ℂ)) *
      MvPolynomial.C (Matrix.det (Matrix.of fun i j : Fin h => colsOf (y' τ) (I i) (j : ℕ))) := by
  have hN := le_of_oe Jc
  let A : Matrix (Fin h) (Fin N') (MvPolynomial (Idx T N N') ℂ) :=
    Matrix.of fun i b => MvPolynomial.C (s τ) * MvPolynomial.X (τ, b, Jc i)
  let B : Matrix (Fin N') (Fin h) (MvPolynomial (Idx T N N') ℂ) :=
    Matrix.of fun b j => MvPolynomial.C (colsOf (y' τ) b (j : ℕ))
  have hAB : (MvPolynomial.aeval (gD s y')).mapMatrix (Matrix.of fun i j : Fin h =>
      if hj : (j : ℕ) < N then (MvPolynomial.X (τ, Jc i, ⟨j, hj⟩) : MvPolynomial (FrV T N) ℂ)
      else 0) = A * B := by
    refine Matrix.ext fun i j => ?_
    have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 hN
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, dif_pos hj,
      MvPolynomial.aeval_X, gD, Matrix.mul_apply, A, B, colsOf]
    apply Finset.sum_congr rfl
    intro b _
    rw [MvPolynomial.C_mul]
    ring
  rw [AlgHom.map_det, hAB, cauchyBinet]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  · rw [← Matrix.det_transpose (A.submatrix id I)]
    rfl
  · rw [RingHom.map_det]
    rfl
end PI.IsoDerivBFintype
