-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CommMult.mInt_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:38:53.870814+00:00
-- url     : https://prove2.me/submissions/856c3b57-b994-4901-9ab8-ef4b514aae37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_IntegrableEntry

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
theorem _root_.solution (μ : Measure H) [μ.IsMulLeftInvariant] {m n : Type} (F : H → Matrix m n ℂ)
    (g : H) : mInt μ (fun h => F (g * h)) = mInt μ F := by
  ext i j
  simp only [mInt, Matrix.of_apply]
  exact integral_mul_left_eq_self (fun h => F h i j) g
end PI.UnitaryGroupMassFormula.CommMult
