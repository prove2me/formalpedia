-- Prove2me | solution 1 for PI.VolStabSW.hasDens_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:29.213798+00:00
-- url     : https://prove2.me/submissions/0b2ddc5d-fa4b-4422-99f5-1af9355f50e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCos
import Theorems.Thm_PI_VolStabSW_hasDens_zero
import Theorems.Thm_PI_VolStabSW_HasDens_add

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
namespace PI.VolStabSW
theorem _root_.solution [IsFiniteMeasureOnCompacts ν] {κ : Type} (φ : κ → V → ℝ) (g : κ → X → ℝ) :
    ∀ T : Finset κ, (∀ i ∈ T, HasDens μ f ι ν (φ i) (g i)) →
      HasDens μ f ι ν (fun v => ∑ i ∈ T, φ i v) (fun b => ∑ i ∈ T, g i b) := by
  intro T
  induction T using Finset.cons_induction with
  | empty =>
    intro _
    simpa using (hasDens_zero : HasDens μ f ι ν (fun _ => 0) (fun _ => 0))
  | cons a s ha ih =>
    intro hT
    have h1 := hT a (Finset.mem_cons_self a s)
    have h2 := ih (fun i hi => hT i (Finset.mem_cons_of_mem hi))
    simpa [Finset.sum_cons] using h1.add h2
end PI.VolStabSW
