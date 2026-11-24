-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CdHaarScale.Main.umat_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:34.443881+00:00
-- url     : https://prove2.me/submissions/78a1c3c1-f4d5-42cc-a389-9834ce7266b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main
namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} :
    Function.Injective (PI.CdHaarScale.umat (ε := ε)) := by
  intro a b h
  exact Subtype.ext (Units.ext h)
end PI.UnitaryGroupMassFormula.CdHaarScale.Main
