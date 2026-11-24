-- Prove2me | solution 1 for PI.VolStabW.VolAAW.algebraMap_AF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:15:47.012874+00:00
-- url     : https://prove2.me/submissions/94fdba9e-bcf5-4497-b417-0f85fefce42e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
variable {F : Type} [Field F] [NumberField F]
namespace PI.VolStabW.VolAAW
theorem _root_.solution (a : F) :
    algebraMap F (AF F) a = pairA F (algebraMap F (Ainf F) a) 0 + pairA F 0 (algebraMap F (Af F) a) := by
  refine Prod.ext ?_ ?_
  · show (algebraMap F (AF F) a).1 = algebraMap F (Ainf F) a + 0
    rw [add_zero]
    rfl
  · show (algebraMap F (AF F) a).2 = 0 + algebraMap F (Af F) a
    rw [zero_add]
    rfl
end PI.VolStabW.VolAAW
