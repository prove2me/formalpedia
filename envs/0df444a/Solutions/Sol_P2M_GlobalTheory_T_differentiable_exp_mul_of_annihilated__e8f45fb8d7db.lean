-- Prove2me | solution 1 for P2M_GlobalTheory_T_differentiable_exp_mul_of_annihilated__e8f45fb8d7db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:23.683576+00:00
-- url     : https://prove2.me/submissions/ed4c8020-7daf-40a9-ab0d-5d302ccb585f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DifferentiableExpMulOfAnnihilated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DifferentiableExpMulOfAnnihilatedStatement
import Theorems.Thm_GlobalTheory_differentiable_exp_mul_of_annihilated


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℝ f → (∀ w z : Fin g → ℂ, (fderiv ℝ f w z + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star z)).im : ℂ) * f w) + Complex.I * (fderiv ℝ f w (Complex.I • z) + Real.pi * Complex.I * ((w ⬝ᵥ Hm.mulVec (star (Complex.I • z))).im : ℂ) * f w) = 0) → Differentiable ℂ fun w : Fin g → ℂ => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f w := by
  first | exact @GlobalTheory.differentiable_exp_mul_of_annihilated | exact GlobalTheory.differentiable_exp_mul_of_annihilated | (intros; apply GlobalTheory.differentiable_exp_mul_of_annihilated <;> assumption)
end _root_.GlobalTheory.T
