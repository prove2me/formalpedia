-- Prove2me | solution 1 for PI.OmFibreUniq.W.td_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:06.166076+00:00
-- url     : https://prove2.me/submissions/4a0160c3-e852-41be-9efb-e37002596cc4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_UniqGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_GramMapFibreExistence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_GramMapFibreUniqueness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology
open PI.OmFibreUniq PI.VolStabSW PI.VolStabSW.TensAllW
open scoped TensorProduct
namespace PI.OmFibreUniq.W
theorem _root_.solution {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    [TotallyDisconnectedSpace α] (e : β → α) (he : Continuous e) (hi : Function.Injective e) :
    TotallyDisconnectedSpace β :=
  ⟨fun t _ ht x hx y hy =>
    hi ((isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (ht.image e he.continuousOn)) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩
end PI.OmFibreUniq.W
