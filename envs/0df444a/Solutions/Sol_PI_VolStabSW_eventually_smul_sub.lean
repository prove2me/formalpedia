-- Prove2me | solution 1 for PI.VolStabSW.eventually_smul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:10.984127+00:00
-- url     : https://prove2.me/submissions/6b7846e9-a4e9-4280-9baa-3bcd8ecc3045

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallySmulSub

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
open Topology Filter Set
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]
namespace PI.VolStabSW
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (S : Set W) (hS : IsCompact S) (s : ℕ → K)
    (hs : Tendsto s atTop (𝓝 0)) (N : Set W) (hN : N ∈ 𝓝 (0 : W)) :
    ∃ k, ∀ p ∈ S, s k • p ∈ N := by
  have hev : ∀ᶠ c in 𝓝 (0 : K), ∀ p ∈ S, c • p ∈ N :=
    hS.eventually_forall_of_forall_eventually fun p _ => by
      have h0 : Tendsto (fun z : K × W => z.1 • z.2) (𝓝 ((0 : K), p)) (𝓝 ((0 : K) • p)) :=
        continuous_smul.continuousAt
      rw [zero_smul] at h0
      exact h0 hN
  exact (hs.eventually hev).exists
end PI.VolStabSW
