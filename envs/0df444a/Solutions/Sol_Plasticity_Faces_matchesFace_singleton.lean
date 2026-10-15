-- Prove2me | solution 1 for Plasticity.Faces.matchesFace_singleton
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:36:00.835835+00:00
-- url     : https://prove2.me/submissions/24d69d0a-2d2d-4cbd-832a-ef0dd5dbfeed

import Definitions.Def_Plasticity_Faces
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_BallMap_norm_map_le
import Theorems.Thm_Plasticity_BallMap_mem_sphere_of_map_mem_sphere
import Theorems.Thm_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere
import Theorems.Thm_Plasticity_BallMap_map_neg_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_mem_extremePoints_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_map_smul_of_map_mem_extremePoints

namespace Sol_Plasticity_Faces_matchesFace_singleton

/-- The basic facts of the cards `Plasticity.BallMap.*` (claim U01), bundled for this file. -/
theorem ballMap_facts {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1)) :
    F 0 = 0 ∧
    (∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x‖ ≤ ‖x‖) ∧
    (∀ x ∈ Metric.closedBall (0 : X) 1, F x ∈ Metric.sphere (0 : Y) 1 → x ∈ Metric.sphere (0 : X) 1) ∧
    (∀ x ∈ Metric.closedBall (0 : X) 1, F x ∈ (Metric.closedBall (0 : Y) 1).extremePoints ℝ →
      x ∈ (Metric.closedBall (0 : X) 1).extremePoints ℝ ∧ F (-x) = -F x ∧
        ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x) ∧
    (Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1) →
      ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x‖ = ‖x‖) :=
  ⟨Plasticity.BallMap.map_zero_of_surjOn F hbij.surjOn hlip,
    fun x hx => Plasticity.BallMap.norm_map_le F hbij.surjOn hlip x hx,
    fun x hx hs => Plasticity.BallMap.mem_sphere_of_map_mem_sphere F hbij.surjOn hlip x hx hs,
    fun x hx he => ⟨Plasticity.BallMap.mem_extremePoints_of_map_mem_extremePoints F hbij hlip x hx he,
      Plasticity.BallMap.map_neg_of_map_mem_extremePoints F hbij hlip x hx he,
      fun t ht => Plasticity.BallMap.map_smul_of_map_mem_extremePoints F hbij hlip x hx he t ht⟩,
    fun hs x hx => Plasticity.BallMap.norm_map_eq_of_mapsTo_sphere F hbij.surjOn hlip hs x hx⟩

end Sol_Plasticity_Faces_matchesFace_singleton

open Plasticity
open scoped Pointwise

/-- A zero-dimensional sphere face `{e}`: its point `e` is an extreme point of the unit ball, so
by the cards `Plasticity.BallMap.*` its unique preimage `x` is an extreme point of the unit ball
in the sphere, `F (-x) = -e` and `F (t • x) = t • e`. -/
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (e : Y) (hC : IsSphereFace ({e} : Set Y)) :
    MatchesFace F {e} := by
  obtain ⟨-, -, hsub, hext⟩ := hC
  have heS : e ∈ Metric.sphere (0 : Y) 1 := hsub rfl
  have heB : e ∈ Metric.closedBall (0 : Y) 1 := Metric.sphere_subset_closedBall heS
  have heE : e ∈ (Metric.closedBall (0 : Y) 1).extremePoints ℝ := isExtreme_singleton.mp hext
  obtain ⟨x, hxB, hFx⟩ := hbij.surjOn heB
  obtain ⟨-, -, hsph, hextc, -⟩ := Sol_Plasticity_Faces_matchesFace_singleton.ballMap_facts F hbij hlip
  have hxS : x ∈ Metric.sphere (0 : X) 1 := hsph x hxB (hFx ▸ heS)
  obtain ⟨hxE, hneg, hline⟩ := hextc x hxB (hFx ▸ heE)
  rw [hFx] at hneg hline
  have hD : Metric.closedBall (0 : X) 1 ∩ F ⁻¹' {e} = {x} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzB, hz⟩
      exact hbij.injOn hzB hxB (hz.trans hFx.symm)
    · rintro rfl
      exact ⟨hxB, hFx⟩
  have hnxB : -x ∈ Metric.closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, norm_neg, ← mem_closedBall_zero_iff]; exact hxB
  have hDneg : Metric.closedBall (0 : X) 1 ∩ F ⁻¹' {-e} = {-x} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzB, hz⟩
      exact hbij.injOn hzB hnxB (hz.trans hneg.symm)
    · rintro rfl
      exact ⟨hnxB, hneg⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hD]
    exact ⟨Set.singleton_nonempty x, convex_singleton x, Set.singleton_subset_iff.mpr hxS,
      isExtreme_singleton.mpr hxE⟩
  · rw [hD]; exact isCompact_singleton
  · rw [hD, vectorSpan_singleton]; infer_instance
  · rw [hD, vectorSpan_singleton, vectorSpan_singleton, finrank_bot, finrank_bot]
  · rw [hD, Set.neg_singleton, Set.neg_singleton]; exact hDneg
  · rw [hD, intrinsicFrontier_singleton, intrinsicFrontier_singleton, Set.preimage_empty,
      Set.inter_empty]
  · rw [hD, extremePoints_singleton, extremePoints_singleton]; exact hD
  · intro t ht
    rw [hD, Set.smul_set_singleton, Set.smul_set_singleton, Set.image_singleton,
      hline t ⟨by linarith [ht.1], ht.2⟩]
