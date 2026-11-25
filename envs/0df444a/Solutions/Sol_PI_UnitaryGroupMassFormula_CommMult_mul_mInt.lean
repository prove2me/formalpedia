-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CommMult.mul_mInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:01.791674+00:00
-- url     : https://prove2.me/submissions/bcd3d58a-a7a3-4a1d-976f-617ed0ac89c3

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
    (A : Matrix l m ℂ) {F : H → Matrix m n ℂ} (hF : Continuous F) :
    A * mInt μ F = mInt μ (fun h => A * F h) := by
  ext i j
  simp only [mInt, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ (fun k _ => (integrable_entry μ hF k j).const_mul (A i k))]
  simp only [integral_const_mul]
end PI.UnitaryGroupMassFormula.CommMult
