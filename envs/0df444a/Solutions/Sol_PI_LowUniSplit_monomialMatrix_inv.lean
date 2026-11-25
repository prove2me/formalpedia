-- Prove2me | solution 1 for PI.LowUniSplit.monomialMatrix_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:37.801477+00:00
-- url     : https://prove2.me/submissions/1df4488e-2a07-4b25-bad4-d8fc8f9cdfd8

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
import Theorems.Thm_PI_LowUniSplit_monoInv_mul

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
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    (monoP w d)⁻¹ = monoInv w d :=
  Matrix.inv_eq_left_inv (monoInv_mul w d hd)
end PI.LowUniSplit
