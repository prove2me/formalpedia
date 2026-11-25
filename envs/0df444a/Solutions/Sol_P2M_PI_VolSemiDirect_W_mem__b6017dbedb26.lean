-- Prove2me | solution 1 for P2M_PI_VolSemiDirect_W_mem__b6017dbedb26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:49:15.056972+00:00
-- url     : https://prove2.me/submissions/a982a8d9-42a7-479a-b4ea-a3ca1bd3cc94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_VolumeQuotientHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open MeasureTheory
namespace PI.VolSemiDirect.W
theorem _root_.solution {X : Type} [Group X] {Γ K : Subgroup X} (γ : ratG Γ K) : ((γ : K) : X) ∈ Γ := by
  have := Subgroup.mem_subgroupOf.mp γ.2
  exact (Subgroup.mem_inf.mp this).1
end PI.VolSemiDirect.W
