-- Prove2me | solution 1 for PI.VolStabW.orb_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:23.794814+00:00
-- url     : https://prove2.me/submissions/90f4b285-f10c-4e69-a960-6718e946ba43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
import Theorems.Thm_PI_VolStabW_orb_mk


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]
namespace PI.VolStabW
theorem _root_.solution (x0 : X) (hc : Continuous fun g : G => g • x0) :
    Continuous (fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) := by
  rw [(QuotientGroup.isQuotientMap_mk (MulAction.stabilizer G x0)).continuous_iff]
  have : ((fun q : G ⧸ MulAction.stabilizer G x0 => q.out • x0) ∘ QuotientGroup.mk) =
      fun g => g • x0 := funext (orb_mk x0)
  rw [this]
  exact hc
end PI.VolStabW
