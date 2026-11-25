-- Prove2me | solution 1 for PI.OddDualWeyl.hermitianDiagonalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:10:57.227497+00:00
-- url     : https://prove2.me/submissions/154e947f-443d-43ed-8bbd-29aa859f1eb3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_rowGen_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open Hom
namespace PI.OddDualWeyl
theorem _root_.solution : Diag := by
  intro R _ k a j d f hf
  unfold rowDiv
  rw [rowGen_diag a hf, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow]
end PI.OddDualWeyl
