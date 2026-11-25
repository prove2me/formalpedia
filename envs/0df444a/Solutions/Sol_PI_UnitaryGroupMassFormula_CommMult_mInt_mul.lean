-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CommMult.mInt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:58.111659+00:00
-- url     : https://prove2.me/submissions/caa0f530-8541-4b39-b79b-a194a2935a21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_IntegrableEntry
import Theorems.Thm_PI_UnitaryGroupMassFormula_CommMult_integrable_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CommMult
open MeasureTheory Matrix
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]
namespace PI.UnitaryGroupMassFormula.CommMult
theorem _root_.solution (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {l m n : Type} [Fintype m]
    {F : H → Matrix l m ℂ} (hF : Continuous F) (B : Matrix m n ℂ) :
    mInt μ F * B = mInt μ (fun h => F h * B) := by
  ext i j
  simp only [mInt, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ (fun k _ => (integrable_entry μ hF i k).mul_const (B k j))]
  simp only [integral_mul_const]
end PI.UnitaryGroupMassFormula.CommMult
