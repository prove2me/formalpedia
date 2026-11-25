-- Prove2me | solution 1 for PI.VolStabSW.isCompact_cos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:55:40.532066+00:00
-- url     : https://prove2.me/submissions/1230e26b-3402-430d-b936-fa56324f7f5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCos

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
open MeasureTheory Topology Set Filter
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}
omit [MeasurableSpace V] [OpensMeasurableSpace V]
namespace PI.VolStabSW
theorem _root_.solution (Λ : AddSubgroup V) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    IsCompact {z | z - y ∈ Λ} := by
  have he : {z | z - y ∈ Λ} = (fun w => w + y) '' (Λ : Set V) := by
    ext z
    constructor
    · intro hz
      exact ⟨z - y, hz, sub_add_cancel z y⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [he]
  exact hΛc.image (continuous_add_right y)
end PI.VolStabSW
