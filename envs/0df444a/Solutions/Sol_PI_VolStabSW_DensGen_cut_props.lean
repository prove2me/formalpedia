-- Prove2me | solution 1 for PI.VolStabSW.DensGen.cut_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:50:24.995804+00:00
-- url     : https://prove2.me/submissions/b920b2e0-b31f-476c-bcf9-d990fce78d9c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.DensGen
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}
namespace PI.VolStabSW.DensGen
theorem _root_.solution {f' : V → X} (hf' : Continuous f') (q : V → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (ψ : X → ℝ) (hψ : Continuous ψ) (C : Set X) (hC : IsClosed C)
    (hψC : ∀ x, ψ x ≠ 0 → x ∈ C) (hCU : ∀ v, f' v ∈ C → v ∈ U) :
    Continuous (fun v => q v * ψ (f' v)) ∧ HasCompactSupport (fun v => q v * ψ (f' v)) ∧
      tsupport (fun v => q v * ψ (f' v)) ⊆ U := by
  refine ⟨hq.mul (hψ.comp hf'), hqs.mul_right, ?_⟩
  have h1 : tsupport (fun v => q v * ψ (f' v)) ⊆ tsupport (fun v => ψ (f' v)) :=
    tsupport_mul_subset_right
  have h2 : tsupport (fun v => ψ (f' v)) ⊆ f' ⁻¹' C := by
    apply closure_minimal _ (hC.preimage hf')
    intro v hv
    exact hψC (f' v) hv
  exact fun v hv => hCU v (h2 (h1 hv))
end PI.VolStabSW.DensGen
