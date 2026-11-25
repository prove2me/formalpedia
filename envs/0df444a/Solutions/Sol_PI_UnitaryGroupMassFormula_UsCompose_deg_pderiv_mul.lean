-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.deg_pderiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:17.867206+00:00
-- url     : https://prove2.me/submissions/926c8ad1-4ac6-426e-af49-fc2c6d8b20b2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Theorems.Thm_Bl_PartialDerivativeDegree_goal1


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
theorem _root_.solution {σ : Type*} (i : σ) (q L : MvPolynomial σ ℂ) (hL : L.totalDegree ≤ 1) :
    (pderiv i q * L).totalDegree ≤ q.totalDegree := by
  first | exact Bl.PartialDerivativeDegree.goal1 .. | (apply Bl.PartialDerivativeDegree.goal1 <;> assumption) | (intros; apply Bl.PartialDerivativeDegree.goal1 <;> assumption) | (apply @Bl.PartialDerivativeDegree.goal1 <;> assumption) | (intros; apply @Bl.PartialDerivativeDegree.goal1 <;> assumption) | (apply @Bl.PartialDerivativeDegree.goal1 <;> first | assumption | infer_instance) | exact @Bl.PartialDerivativeDegree.goal1 σ i q L hL | exact @Bl.PartialDerivativeDegree.goal1 σ i q L | exact @Bl.PartialDerivativeDegree.goal1 σ i q | exact @Bl.PartialDerivativeDegree.goal1 σ i | exact @Bl.PartialDerivativeDegree.goal1 σ
end PI.UnitaryGroupMassFormula.UsCompose
