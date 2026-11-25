-- Prove2me | solution 1 for PI.GaugeCharW.isOpen_intSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:42:01.620284+00:00
-- url     : https://prove2.me/submissions/18be2ce6-213e-4e5f-b22f-50f55881330b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GaugeGap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IntInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerSubgroupIntersection_IsOpenIntSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GaugeCharW
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable (F : Type) [Field F] [NumberField F]
namespace PI.GaugeCharW
theorem _root_.solution (h3 : OpenInt) : IsOpen (intSub F : Set (AF F)) := by
  exact (h3 F).preimage (continuous_snd : Continuous (Prod.snd : Ainf F × Af F → Af F))
end PI.GaugeCharW
