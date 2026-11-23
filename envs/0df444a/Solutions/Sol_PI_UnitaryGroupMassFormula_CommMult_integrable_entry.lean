-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CommMult.integrable_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:53.250517+00:00
-- url     : https://prove2.me/submissions/5d090635-cf8e-4700-a08d-c2d394affdb4

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
theorem _root_.solution (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {m n : Type}
    {F : H → Matrix m n ℂ} (hF : Continuous F) (i : m) (j : n) :
    Integrable (fun h => F h i j) μ :=
  (hF.matrix_elem i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end PI.UnitaryGroupMassFormula.CommMult
