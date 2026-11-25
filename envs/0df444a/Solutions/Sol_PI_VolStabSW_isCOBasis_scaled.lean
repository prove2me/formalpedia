-- Prove2me | solution 1 for PI.VolStabSW.isCOBasis_scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:55:36.044239+00:00
-- url     : https://prove2.me/submissions/96bba7cf-db02-40a4-bc76-c1559c4fd0bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVNA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct
private theorem exists_pow_smul_mem_nhds_of_isCompact' {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : Set V) (hLc : IsCompact L)
    (π : 𝕜) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) (N : Set V) (hN : N ∈ 𝓝 (0 : V)) :
    ∃ k : ℕ, ∀ y ∈ L, π ^ k • y ∈ N := by
  have h : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ L, c • y ∈ N := by
    refine hLc.eventually_forall_of_forall_eventually fun y _ => ?_
    have ht : Tendsto (fun z : 𝕜 × V => z.1 • z.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y)) :=
      continuous_smul.continuousAt
    rw [zero_smul] at ht
    exact ht hN
  exact (hπ.eventually h).exists
end PI.VolStabSW
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : IsCOBasis (scaledB 𝕜 L) := by
  intro N hN
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_nhds_of_isCompact' (L : Set V) hLc π hπ N hN
  have hc : π ^ k ≠ 0 := pow_ne_zero k h0
  have himg : ((L.map (DistribMulAction.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := by
    ext x
    simp
  refine ⟨L.map (DistribMulAction.toAddMonoidHom V (π ^ k)), ⟨π ^ k, hc, rfl⟩, ?_, ?_, ?_⟩
  · rw [himg]
    exact isOpenMap_smul₀ hc _ hLo
  · rw [himg]
    exact hLc.image (continuous_const_smul _)
  · rw [himg]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy
end PI.VolStabSW
