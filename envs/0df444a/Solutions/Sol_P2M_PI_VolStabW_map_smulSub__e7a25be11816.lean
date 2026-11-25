-- Prove2me | solution 1 for P2M_PI_VolStabW_map_smulSub__e7a25be11816
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:47.062866+00:00
-- url     : https://prove2.me/submissions/cb78a892-8084-49dc-9d43-118fe60f2386

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
import Theorems.Thm_PI_VolStabW_mem_smulSub


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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix
namespace PI.VolStabW
theorem _root_.solution {K V X : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup X]
    [Module K X] (D : V →+ X) (hDs : ∀ (t : K) w, D (t • w) = t • D w) (t : K)
    (L : AddSubgroup V) : (smulSub t L).map D = smulSub t (L.map D) := by
  ext z
  rw [AddSubgroup.mem_map, mem_smulSub]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨l, hl, rfl⟩ := (mem_smulSub _ _ _).1 hw
    exact ⟨D l, AddSubgroup.mem_map_of_mem _ hl, (hDs t l).symm⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hq
    exact ⟨t • l, (mem_smulSub _ _ _).2 ⟨l, hl, rfl⟩, hDs t l⟩
end PI.VolStabW
