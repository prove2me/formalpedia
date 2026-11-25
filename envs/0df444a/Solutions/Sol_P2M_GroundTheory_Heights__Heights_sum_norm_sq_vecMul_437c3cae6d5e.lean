-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sum_norm_sq_vecMul_437c3cae6d5e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:40.504138+00:00
-- url     : https://prove2.me/submissions/c3c386b0-24e8-4783-bdca-7e7d56791dd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (r : Fin n → ℂ) :
    ∑ j, ‖(r ᵥ* A) j‖ ^ 2 = ∑ j, ‖r j‖ ^ 2 := by
  have key : ∀ s : Fin n → ℂ, ((∑ j, ‖s j‖ ^ 2 : ℝ) : ℂ) = s ⬝ᵥ star s := by
    intro s
    simp [dotProduct, Complex.mul_conj']
  apply Complex.ofReal_injective
  rw [key (r ᵥ* A), key r, Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff).1 hA, Matrix.vecMul_one]
end GroundTheory.Heights₂.Heights
