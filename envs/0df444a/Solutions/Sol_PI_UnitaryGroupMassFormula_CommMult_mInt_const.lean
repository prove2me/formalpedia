-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CommMult.mInt_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:42.238611+00:00
-- url     : https://prove2.me/submissions/f0de8d79-21f4-4e57-b7d4-fd11d741ec45

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
theorem _root_.solution (μ : Measure H) {m n : Type} (C : Matrix m n ℂ) :
    mInt μ (fun _ => C) = μ.real Set.univ • C := by
  ext i j
  simp [mInt, integral_const]
end PI.UnitaryGroupMassFormula.CommMult
