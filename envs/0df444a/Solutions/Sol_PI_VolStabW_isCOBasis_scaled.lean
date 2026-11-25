-- Prove2me | solution 1 for PI.VolStabW.isCOBasis_scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:35.060448+00:00
-- url     : https://prove2.me/submissions/e45d5d23-64b2-401e-b4a8-54e5e79403f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVNA

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
  Topology Filter
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : IsCOBasis (scaledB 𝕜 L) := by
  intro N hN
  have hP : ∀ x ∈ (L : Set V), ∀ᶠ p : 𝕜 × V in 𝓝 ((0 : 𝕜), x), p.1 • p.2 ∈ N := by
    intro x _
    have h : Tendsto (fun p : 𝕜 × V => p.1 • p.2) (𝓝 ((0 : 𝕜), x)) (𝓝 (0 : V)) := by
      simpa using (continuous_smul : Continuous fun p : 𝕜 × V => p.1 • p.2).tendsto ((0 : 𝕜), x)
    exact h hN
  have hev := hLc.eventually_forall_of_forall_eventually (x₀ := (0 : 𝕜))
    (P := fun (c : 𝕜) (y : V) => c • y ∈ N) hP
  obtain ⟨k, hk⟩ := (hπ.eventually hev).exists
  have hk0 : π ^ k ≠ 0 := pow_ne_zero k h0
  refine ⟨L.map (DistribMulAction.toAddMonoidHom V (π ^ k)), ⟨π ^ k, hk0, rfl⟩, ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_map]
    exact (Homeomorph.smulOfNeZero (π ^ k) hk0).isOpenMap _ hLo
  · rw [AddSubgroup.coe_map]
    exact hLc.image (continuous_const_smul _)
  · rw [AddSubgroup.coe_map]
    rintro _ ⟨x, hx, rfl⟩
    exact hk x hx
end PI.VolStabW
