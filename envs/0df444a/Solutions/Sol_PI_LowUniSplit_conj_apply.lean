-- Prove2me | solution 1 for PI.LowUniSplit.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:55:21.86065+00:00
-- url     : https://prove2.me/submissions/86938356-ed4f-4d5e-a4ec-0a339bb3a9b7

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
import Theorems.Thm_PI_LowUniSplit_monomialMatrix_inv

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
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.LowUniSplit
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    ((monoP w d)⁻¹ * l * monoP w d) a b = (d a)⁻¹ * l (w a) (w b) * d b := by
  rw [monomialMatrix_inv w d hd]
  simp only [Matrix.mul_apply, monoInv, monoP, Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq', mul_assoc]
end PI.LowUniSplit
