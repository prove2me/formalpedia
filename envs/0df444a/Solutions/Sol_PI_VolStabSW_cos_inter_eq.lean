-- Prove2me | solution 1 for PI.VolStabSW.cos_inter_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:52.098742+00:00
-- url     : https://prove2.me/submissions/f2c692e0-f8bf-40a1-b641-fb7354ff698d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_HenselCountHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHF

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
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
namespace PI.VolStabSW
theorem _root_.solution (Λ0 : AddSubgroup V) (Hn : AddSubgroup X) (G : V → X) (y : V) (T : X) :
    {x | x - y ∈ Λ0} ∩ G ⁻¹' {z | z - T ∈ Hn} = (fun x => -y + x) ⁻¹' hlev Λ0 Hn G y T := by
  ext x
  simp [hlev, neg_add_eq_sub]
end PI.VolStabSW
