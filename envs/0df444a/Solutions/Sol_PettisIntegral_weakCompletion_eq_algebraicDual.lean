-- Prove2me | solution 1 for PettisIntegral.weakCompletion_eq_algebraicDual
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:00:30.678595+00:00
-- url     : https://prove2.me/submissions/de7ef0f4-4ae3-47a1-b2bc-a3843fa001c4

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_weakCompletion_eq_algebraicDual

open PettisIntegral

/-- Hahn–Banach: the continuous dual of a Hausdorff locally convex space separates points. -/
theorem exists_dual_ne_zero {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E]
    [T2Space E] {x : E} (hx : x ≠ 0) : ∃ f : StrongDual 𝕜 E, f x ≠ 0 := by
  let _ : Module ℝ E := .restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  have : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  obtain ⟨f, hf⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hx
  exact ⟨f, fun h => by simp [h] at hf⟩

/-- The set of linear forms on the dual is closed in the product space. -/
theorem isClosed_linear {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] :
    IsClosed {a : StrongDual 𝕜 E → 𝕜 | IsLinearMap 𝕜 a} := by
  have h : {a : StrongDual 𝕜 E → 𝕜 | IsLinearMap 𝕜 a} =
      {a | ∀ x y, a (x + y) = a x + a y} ∩ {a | ∀ (c : 𝕜) x, a (c • x) = c • a x} := by
    ext a
    exact ⟨fun h => ⟨h.map_add, h.map_smul⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [h]
  exact (isClosed_setOfPred_map_add _ _).inter (isClosed_setOfPred_map_smul _ _ id)

/-- Finite interpolation: a linear form on the dual agrees, on any finite set of continuous
functionals, with the evaluation at some vector. -/
theorem exists_eq_on_finset {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] (a : StrongDual 𝕜 E → 𝕜) (ha : IsLinearMap 𝕜 a)
    (s : Finset (StrongDual 𝕜 E)) : ∃ u : E, ∀ φ ∈ s, φ u = a φ := by
  classical
  -- the evaluation map `u ↦ (φ u)_{φ ∈ s}` and the vector `(a φ)_{φ ∈ s}`
  let L : E →ₗ[𝕜] (s → 𝕜) := LinearMap.pi (fun φ : s => (φ : StrongDual 𝕜 E).toLinearMap)
  let v : s → 𝕜 := fun φ => a φ
  by_contra hne
  have hv : v ∉ LinearMap.range L := by
    rintro ⟨u, hu⟩
    exact hne ⟨u, fun φ hφ => congrFun hu ⟨φ, hφ⟩⟩
  -- a linear form on `𝕜^s` vanishing on the range of `L` but not at `v`
  obtain ⟨f, hfv, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  let c : s → 𝕜 := fun i => f (fun j => if i = j then 1 else 0)
  have hfsum : ∀ w : s → 𝕜, f w = ∑ i, w i * c i := by
    intro w
    simpa [c] using LinearMap.pi_apply_eq_sum_univ f w
  -- the corresponding linear combination of the functionals vanishes
  let ψ : StrongDual 𝕜 E := ∑ i : s, c i • (i : StrongDual 𝕜 E)
  have hψ : ψ = 0 := by
    ext u
    have h0 : f (L u) = 0 := by
      have hmem : f (L u) ∈ (LinearMap.range L).map f := ⟨L u, ⟨u, rfl⟩, rfl⟩
      exact (Submodule.mem_bot 𝕜).mp (hf ▸ hmem)
    rw [hfsum] at h0
    rw [_root_.zero_apply, ← h0]
    change (∑ i : s, c i • (i : StrongDual 𝕜 E)) u = _
    rw [_root_.sum_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hfa : f v = a ψ := by
    have hsum : a ψ = ∑ i : s, c i * a (i : StrongDual 𝕜 E) := by
      change (IsLinearMap.mk' a ha) (∑ i : s, c i • (i : StrongDual 𝕜 E)) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
    rw [hsum, hfsum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  exact hfv (by rw [hfa, hψ, ha.map_zero])

end Sol_PettisIntegral_weakCompletion_eq_algebraicDual

open PettisIntegral

theorem solution {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E]
    [T2Space E] :
    Topology.IsEmbedding
        (fun u : WeakSpace 𝕜 E => toWeakCompletion 𝕜 ((toWeakSpace 𝕜 E).symm u)) ∧
      closure (Set.range (fun u : E => toWeakCompletion 𝕜 u)) =
        {a : StrongDual 𝕜 E → 𝕜 | IsLinearMap 𝕜 a} ∧
      IsComplete {a : StrongDual 𝕜 E → 𝕜 | IsLinearMap 𝕜 a} := by
  refine ⟨?_, ?_, ?_⟩
  · -- the pairing `u ↦ (φ ↦ φ u)` is injective by Hahn–Banach
    have hB : Function.Injective (topDualPairing 𝕜 E).flip := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      by_contra hne
      obtain ⟨f, hf⟩ := Sol_PettisIntegral_weakCompletion_eq_algebraicDual.exists_dual_ne_zero
        (𝕜 := 𝕜) hne
      exact hf (by simpa using congrArg (fun g => g f) hx)
    exact WeakBilin.isEmbedding hB
  · apply Set.Subset.antisymm
    · apply closure_minimal _ Sol_PettisIntegral_weakCompletion_eq_algebraicDual.isClosed_linear
      rintro _ ⟨u, rfl⟩
      exact ⟨fun φ ψ => rfl, fun c φ => rfl⟩
    · intro a ha
      rw [mem_closure_iff]
      intro U hU haU
      obtain ⟨I, t, ht, hsub⟩ := isOpen_pi_iff.mp hU a haU
      obtain ⟨u, hu⟩ :=
        Sol_PettisIntegral_weakCompletion_eq_algebraicDual.exists_eq_on_finset a ha I
      refine ⟨toWeakCompletion 𝕜 u, hsub ?_, ⟨u, rfl⟩⟩
      intro φ hφ
      rw [toWeakCompletion_apply, hu φ hφ]
      exact (ht φ hφ).2
  · exact Sol_PettisIntegral_weakCompletion_eq_algebraicDual.isClosed_linear.isComplete
