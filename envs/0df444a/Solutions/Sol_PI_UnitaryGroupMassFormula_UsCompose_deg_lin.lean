-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.deg_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:07.397574+00:00
-- url     : https://prove2.me/submissions/ff73e4c3-7041-4702-a7f2-3ee609944046

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_CX

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
theorem _root_.solution {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : Vr N) : (lin X i).totalDegree ≤ 1 := by
  rcases i with x | x
  · exact (totalDegree_finset_sum _ _).trans (Finset.sup_le fun c _ => deg_CX _ _)
  · exact (totalDegree_finset_sum _ _).trans (Finset.sup_le fun c _ => deg_CX _ _)
end PI.UnitaryGroupMassFormula.UsCompose
