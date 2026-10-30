-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P09.actionCommutator_normal_contains_commutator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:55:25.65293+00:00
-- url     : https://prove2.me/submissions/2d783f94-f3fd-40ad-b19f-8013bc0a0cd7

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P09

open scoped Manifold ContDiff
open QAlgorithms.Papers.Independent.Bridge50.P09

theorem solution
    {EG EH : Type*}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [NormedAddCommGroup EH] [NormedSpace ℝ EH] [FiniteDimensional ℝ EH]
    {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [T2Space G] [T2Space H]
    [SecondCountableTopology G] [SecondCountableTopology H]
    [ChartedSpace EG G] [ChartedSpace EH H]
    [IsManifold (𝓘(ℝ, EG)) ∞ G] [IsManifold (𝓘(ℝ, EH)) ∞ H]
    [LieGroup (𝓘(ℝ, EG)) ∞ G] [LieGroup (𝓘(ℝ, EH)) ∞ H]
    (t : H →* G) (alpha : G →* MulAut H)
    (hCrossed : QAlgorithms.Papers.Independent.Renew46.P18.IsCrossedModule t alpha)
    (ht : ContMDiff (𝓘(ℝ, EH)) (𝓘(ℝ, EG)) ∞ t)
    (ha : ContMDiff ((𝓘(ℝ, EG)).prod (𝓘(ℝ, EH))) (𝓘(ℝ, EH)) ∞
      (fun p : G × H => alpha p.1 p.2)) :
    (actionCommutatorSubgroup (fun g h => alpha g h)).Normal ∧
      commutator H ≤ actionCommutatorSubgroup (fun g h => alpha g h) := by
  have hcomm : commutator H ≤ actionCommutatorSubgroup (fun g h => alpha g h) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ k _
    apply Subgroup.subset_closure
    refine ⟨t k, x⁻¹, ?_⟩
    show _ = x⁻¹⁻¹ * (alpha (t k)) x⁻¹
    rw [hCrossed.2 k x⁻¹, commutatorElement_def]
    group
  refine ⟨⟨fun s hs k => ?_⟩, hcomm⟩
  have h1 : k * s * k⁻¹ * s⁻¹ ∈ actionCommutatorSubgroup (fun g h => alpha g h) := by
    apply hcomm
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top k) (Subgroup.mem_top s)
  have : k * s * k⁻¹ = (k * s * k⁻¹ * s⁻¹) * s := by group
  rw [this]
  exact Subgroup.mul_mem _ h1 hs
