-- Prove2me | solution 1 for PI.VolStabW.eventually_smul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:16.124813+00:00
-- url     : https://prove2.me/submissions/7aefb1e3-a172-4c92-ac3e-7cfacce0e4e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_EventuallySmulSub

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
open Topology Filter Set
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]
namespace PI.VolStabW
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (S : Set W) (hS : IsCompact S) (s : ℕ → K)
    (hs : Tendsto s atTop (𝓝 0)) (N : Set W) (hN : N ∈ 𝓝 (0 : W)) :
    ∃ k, ∀ p ∈ S, s k • p ∈ N := by
  have hP : ∀ p ∈ S, ∀ᶠ q : K × W in 𝓝 ((0 : K), p), q.1 • q.2 ∈ N := by
    intro p _
    have h : Tendsto (fun q : K × W => q.1 • q.2) (𝓝 ((0 : K), p)) (𝓝 (0 : W)) := by
      simpa using (continuous_smul : Continuous fun q : K × W => q.1 • q.2).tendsto ((0 : K), p)
    exact h hN
  have hev := hS.eventually_forall_of_forall_eventually (P := fun (t : K) (p : W) => t • p ∈ N) hP
  exact (hs.eventually hev).exists
end PI.VolStabW
