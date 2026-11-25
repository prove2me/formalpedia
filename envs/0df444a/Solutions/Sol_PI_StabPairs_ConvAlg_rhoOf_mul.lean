-- Prove2me | solution 1 for PI.StabPairs.ConvAlg.rhoOf_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:26:44.152338+00:00
-- url     : https://prove2.me/submissions/ec57eeb2-1817-4ebb-bb2c-1def372c5a34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConvAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairs PI.StabPairs.ConvAlg
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
namespace PI.StabPairs.ConvAlg
theorem _root_.solution (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (hG : IsUnit (Fᴴ * H * F).det) : rhoOf H F W * F = F * W := by
  have hinv : (Fᴴ * H * F)⁻¹ * (Fᴴ * H * F) = 1 := Matrix.nonsing_inv_mul _ hG
  rw [rhoOf, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc F, Matrix.mul_assoc (W - 1),
    Matrix.mul_assoc (Fᴴ * H * F)⁻¹, hinv, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  abel
end PI.StabPairs.ConvAlg
