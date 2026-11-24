-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.deg_CX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:52:10.088973+00:00
-- url     : https://prove2.me/submissions/15590c72-f7dd-432f-901e-1f0e8de7872e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul

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
theorem _root_.solution {σ : Type*} (a : ℂ) (v : σ) : (C a * X v : MvPolynomial σ ℂ).totalDegree ≤ 1 :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
end PI.UnitaryGroupMassFormula.UsCompose
