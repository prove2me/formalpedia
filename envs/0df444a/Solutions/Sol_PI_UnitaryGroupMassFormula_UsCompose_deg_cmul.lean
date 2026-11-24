-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.deg_cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:34:56.197719+00:00
-- url     : https://prove2.me/submissions/572fe96f-e6b4-43bb-a05c-7d32c90355fc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution (c : ℂ) {N : ℕ} (q r : MvPolynomial (Vr N) ℂ) :
    (C c * q * r).totalDegree ≤ q.totalDegree + r.totalDegree := by
  refine (totalDegree_mul _ _).trans (Nat.add_le_add_right ?_ _)
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_C]
end PI.UnitaryGroupMassFormula.UsCompose
