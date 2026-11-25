-- Prove2me | solution 1 for PI.VolStabS.isOpen_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:53.360573+00:00
-- url     : https://prove2.me/submissions/52155194-6762-4adf-a940-512d1fc3738d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_MeasureEqOfCos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Topology Set Filter
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
omit [MeasurableSpace X] [OpensMeasurableSpace X]
namespace PI.VolStabS
theorem _root_.solution (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have e : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x
    simp [thick]
  rw [e]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)
end PI.VolStabS
