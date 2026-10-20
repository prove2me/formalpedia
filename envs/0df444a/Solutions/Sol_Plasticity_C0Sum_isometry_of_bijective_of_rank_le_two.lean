-- Prove2me | solution 1 for Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:04:04.001144+00:00
-- url     : https://prove2.me/submissions/1bdd02d0-920c-4c6c-9841-e4f098da7901

import Definitions.Def_Plasticity_C0Sum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_C0Sum_isometry_of_bijective_of_rank_le_two_reduction
import Theorems.Thm_Plasticity_C0Sum_isometryOn_of_reduced

/-!
CUB109 for blocks of dimension at most two: reduce both c₀ sums to reduced families by linear
isometries (part card `reduction`), transport the ball map, and apply
`Plasticity.C0Sum.isometryOn_of_reduced`.
-/

open Plasticity Metric

theorem solution {ι κ : Type*}
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (E' : κ → Type*) [∀ k, NormedAddCommGroup (E' k)] [∀ k, NormedSpace ℝ (E' k)]
    (hE : ∀ i, Module.rank ℝ (E i) ≤ 2) (hE' : ∀ k, Module.rank ℝ (E' k) ≤ 2)
    (f : Metric.closedBall (0 : c0Sum E) 1 → Metric.closedBall (0 : c0Sum E') 1)
    (hf : LipschitzWith 1 f) (hbij : Function.Bijective f) : Isometry f := by
  classical
  obtain ⟨J, G, _, _, hG, ⟨Ψ⟩⟩ :=
    Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two.reduction E hE
  obtain ⟨J', G', _, _, hG', ⟨Ψ'⟩⟩ :=
    Plasticity.C0Sum.isometry_of_bijective_of_rank_le_two.reduction E' hE'
  have hmem : ∀ y, y ∈ closedBall (0 : c0Sum G) 1 ↔ Ψ y ∈ closedBall (0 : c0Sum E) 1 := by
    intro y
    rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff, Ψ.norm_map]
  have hmem' : ∀ z, Ψ'.symm z ∈ closedBall (0 : c0Sum G') 1 ↔
      z ∈ closedBall (0 : c0Sum E') 1 := by
    intro z
    rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff, Ψ'.symm.norm_map]
  -- the transported map, extended by zero off the ball
  let F : c0Sum G → c0Sum G' := fun y =>
    if hy : Ψ y ∈ closedBall (0 : c0Sum E) 1 then Ψ'.symm (f ⟨Ψ y, hy⟩) else 0
  have hF : ∀ y (hy : Ψ y ∈ closedBall (0 : c0Sum E) 1), F y = Ψ'.symm (f ⟨Ψ y, hy⟩) :=
    fun y hy => dif_pos hy
  have hbijF : Set.BijOn F (closedBall 0 1) (closedBall 0 1) := by
    refine ⟨fun y hy => ?_, fun y hy z hz hyz => ?_, fun w hw => ?_⟩
    · rw [hF y ((hmem y).1 hy)]
      exact (hmem' _).2 (f _).2
    · rw [hF y ((hmem y).1 hy), hF z ((hmem z).1 hz)] at hyz
      have h1 := hbij.1 (Subtype.ext (Ψ'.symm.injective hyz))
      exact Ψ.injective (congrArg Subtype.val h1)
    · have hw' : Ψ' w ∈ closedBall (0 : c0Sum E') 1 := by
        rw [← hmem', LinearIsometryEquiv.symm_apply_apply]
        exact hw
      obtain ⟨⟨x, hx⟩, hfx⟩ := hbij.2 ⟨Ψ' w, hw'⟩
      have hx' : Ψ (Ψ.symm x) ∈ closedBall (0 : c0Sum E) 1 := by
        rw [LinearIsometryEquiv.apply_symm_apply]
        exact hx
      refine ⟨Ψ.symm x, (hmem _).2 hx', ?_⟩
      rw [hF _ hx']
      have h2 : (⟨Ψ (Ψ.symm x), hx'⟩ : closedBall (0 : c0Sum E) 1) = ⟨x, hx⟩ :=
        Subtype.ext (Ψ.apply_symm_apply x)
      rw [h2, hfx, LinearIsometryEquiv.symm_apply_apply]
  have hdist : ∀ y (hy : Ψ y ∈ closedBall (0 : c0Sum E) 1) z
      (hz : Ψ z ∈ closedBall (0 : c0Sum E) 1),
      ‖F y - F z‖ = dist (f ⟨Ψ y, hy⟩) (f ⟨Ψ z, hz⟩) := by
    intro y hy z hz
    rw [hF y hy, hF z hz, ← map_sub, Ψ'.symm.norm_map, Subtype.dist_eq, dist_eq_norm]
  have hdist' : ∀ y (hy : Ψ y ∈ closedBall (0 : c0Sum E) 1) z
      (hz : Ψ z ∈ closedBall (0 : c0Sum E) 1),
      dist (⟨Ψ y, hy⟩ : closedBall (0 : c0Sum E) 1) ⟨Ψ z, hz⟩ = ‖y - z‖ := by
    intro y hy z hz
    rw [Subtype.dist_eq, dist_eq_norm, ← map_sub, Ψ.norm_map]
  have hlipF : LipschitzOnWith 1 F (closedBall 0 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    have hy' := (hmem y).1 hy
    have hz' := (hmem z).1 hz
    rw [dist_eq_norm, dist_eq_norm, hdist y hy' z hz', ← hdist' y hy' z hz']
    simpa using hf.dist_le_mul ⟨Ψ y, hy'⟩ ⟨Ψ z, hz'⟩
  have key := Plasticity.C0Sum.isometryOn_of_reduced G G' hG hG' F hbijF hlipF
  refine Isometry.of_dist_eq fun p q => ?_
  have hp : Ψ (Ψ.symm p.1) ∈ closedBall (0 : c0Sum E) 1 := by
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact p.2
  have hq : Ψ (Ψ.symm q.1) ∈ closedBall (0 : c0Sum E) 1 := by
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact q.2
  have e1 : (⟨Ψ (Ψ.symm p.1), hp⟩ : closedBall (0 : c0Sum E) 1) = p :=
    Subtype.ext (Ψ.apply_symm_apply p.1)
  have e2 : (⟨Ψ (Ψ.symm q.1), hq⟩ : closedBall (0 : c0Sum E) 1) = q :=
    Subtype.ext (Ψ.apply_symm_apply q.1)
  have h := key (Ψ.symm p.1) ((hmem _).2 hp) (Ψ.symm q.1) ((hmem _).2 hq)
  rw [hdist _ hp _ hq, ← hdist' _ hp _ hq, e1, e2] at h
  exact h
