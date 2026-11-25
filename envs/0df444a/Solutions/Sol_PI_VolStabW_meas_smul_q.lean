-- Prove2me | solution 1 for PI.VolStabW.meas_smul_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:40.403814+00:00
-- url     : https://prove2.me/submissions/229632a2-fa78-4f0a-ae9a-e8679fc4c7d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ExStabU

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
open scoped TensorProduct ENNReal NNReal Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabW
theorem _root_.solution (H : Subgroup G) (g : G) : Measurable (fun q : G ⧸ H => g • q) := by
  apply measurable_from_quotient.2
  have : ((fun q : G ⧸ H => g • q) ∘ Quotient.mk'') = (QuotientGroup.mk : G → G ⧸ H) ∘ (g * ·) := by
    funext k
    rfl
  rw [this]
  exact measurable_quotient_mk''.comp (measurable_const_mul g)
end PI.VolStabW
