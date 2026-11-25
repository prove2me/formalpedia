-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.degDP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:06:42.968452+00:00
-- url     : https://prove2.me/submissions/2020ea75-d7ef-42d1-a98d-e02ef4943cd4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_pderiv_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (q : MvPolynomial (Vr N) ℂ) :
    (dP X q).totalDegree ≤ q.totalDegree :=
  (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => deg_pderiv_mul i q _ (deg_lin X i))
end PI.UnitaryGroupMassFormula.UsCompose
