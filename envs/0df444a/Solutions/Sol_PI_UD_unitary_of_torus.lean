-- Prove2me | solution 1 for PI.UD.unitary_of_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:31:41.20621+00:00
-- url     : https://prove2.me/submissions/74bd52b9-788e-4f48-a4be-78fc68549d15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_GramStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UD
namespace PI.UD
theorem _root_.solution {n : ℕ} (w v : Matrix (Fin n) (Fin n) ℂ) (hw : wᴴ * w = 1)
    (hv : vᴴ * v = 1) (t : Fin n → ℂ) (ht : ∀ k, ‖t k‖ = 1) :
    (w * diagonal t * v)ᴴ * (w * diagonal t * v) = 1 := by
  have hd : (diagonal t)ᴴ * diagonal t = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ht k]
    norm_num
  simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc wᴴ, hw, Matrix.one_mul, ← Matrix.mul_assoc (diagonal t)ᴴ, hd,
    Matrix.one_mul, hv]
end PI.UD
