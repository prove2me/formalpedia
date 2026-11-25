-- Prove2me | solution 1 for PI.VolStabSW.densLC_of_cos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:32.172994+00:00
-- url     : https://prove2.me/submissions/b58cdc0b-c127-42dd-9fe0-c699d81854eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCos
import Theorems.Thm_PI_VolStabSW_densLC_of_cosB

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
theorem _root_.solution [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (U : Set V)
    (hNA : HasCOSub V) (h : DensCos μ f ι ν U) : DensOn (IsLCcOn U) μ f ι ν := by
  refine densLC_of_cosB U (fun _ => True) ?_ ?_
  · intro N hN
    first
      | (obtain ⟨Λ, h1, h2, h3⟩ := hNA N hN
         exact ⟨Λ, trivial, h1, h2, h3⟩)
      | (obtain ⟨Λ, h1, h2, h3⟩ := hNA hN
         exact ⟨Λ, trivial, h1, h2, h3⟩)
      | (obtain ⟨Λ, h2, h1, h3⟩ := hNA N hN
         exact ⟨Λ, trivial, h1, h2, h3⟩)
  · intro x hx
    obtain ⟨N, hN, h'⟩ := h x hx
    exact ⟨N, hN, fun y hy Λ _ => h' y hy Λ⟩
end PI.VolStabSW
