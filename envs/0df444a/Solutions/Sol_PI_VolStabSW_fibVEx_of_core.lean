-- Prove2me | solution 1 for PI.VolStabSW.fibVEx_of_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:41.550176+00:00
-- url     : https://prove2.me/submissions/7147daf1-168e-4211-b6bc-47afa4fc5450

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibDis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExOmTOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibTop
import Theorems.Thm_PI_VolStabSW_tensAll_of
import Theorems.Thm_PI_VolStabSW_DiscreteGroups_fibOfDens_holds
import Theorems.Thm_PI_VolStabSW_fibVEx_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (h1 : FreeOpen) (h2 : DensV) : FibVEx := fibVEx_of DiscreteGroups.fibOfDens_holds (tensAll_of h1) h2
end PI.VolStabSW
