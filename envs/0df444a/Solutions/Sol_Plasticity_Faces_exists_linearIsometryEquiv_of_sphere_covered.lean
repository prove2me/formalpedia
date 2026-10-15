-- Prove2me | solution 1 for Plasticity.Faces.exists_linearIsometryEquiv_of_sphere_covered
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:46:45.614977+00:00
-- url     : https://prove2.me/submissions/9883e8c3-33d5-46ce-9b89-4bab06e36fa8

import Definitions.Def_Plasticity_Faces
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_Faces_matchesFace_of_finiteDimensional
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn
import Theorems.Thm_Plasticity_BallMap_norm_map_le
import Theorems.Thm_Plasticity_BallMap_mem_sphere_of_map_mem_sphere
import Theorems.Thm_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere
import Theorems.Thm_Plasticity_BallMap_map_neg_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_mem_extremePoints_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_BallMap_map_smul_of_map_mem_extremePoints
import Theorems.Thm_Plasticity_U10

namespace Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered

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

end Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered


open Plasticity
open scoped Pointwise

namespace Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered

/-- The linear isometry equivalence between two trivial normed spaces. -/
noncomputable def lieOfSubsingleton (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Subsingleton X] [Subsingleton Y] : X ≃ₗᵢ[ℝ] Y :=
  { LinearEquiv.ofSubsingleton X Y with
    norm_map' := fun x => by
      rw [Subsingleton.elim x 0, norm_zero]
      exact norm_eq_zero.mpr (Subsingleton.elim _ _) }

/-- Under the cover hypothesis, `F` maps the unit sphere into the unit sphere. -/
theorem maps_sphere {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hcover : ∀ y ∈ Metric.sphere (0 : Y) 1, ∃ C : Set Y,
      IsSphereFace C ∧ FiniteDimensional ℝ (vectorSpan ℝ C) ∧ y ∈ C) :
    Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1) := by
  intro x hx
  have hxn : ‖x‖ = 1 := by simpa using hx
  have hxB : x ∈ Metric.closedBall (0 : X) 1 := Metric.sphere_subset_closedBall hx
  set y := F x with hy
  have hyB : y ∈ Metric.closedBall (0 : Y) 1 := hbij.mapsTo hxB
  have hyle : ‖y‖ ≤ 1 := by simpa using hyB
  have hF0 : F 0 = 0 := (Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered.ballMap_facts F hbij hlip).1
  have h0B : (0 : X) ∈ Metric.closedBall (0 : X) 1 := Metric.mem_closedBall_self zero_le_one
  have hy0 : y ≠ 0 := by
    intro h
    have : x = 0 := hbij.injOn hxB h0B (by rw [← hy, h, hF0])
    rw [this, norm_zero] at hxn
    exact zero_ne_one hxn
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  set u := ‖y‖⁻¹ • y with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hypos.ne']
  have huS : u ∈ Metric.sphere (0 : Y) 1 := by simpa using hun
  obtain ⟨C, hC, hfin, huC⟩ := hcover u huS
  obtain ⟨hD, -, -, -, -, -, -, hcone⟩ :=
    Plasticity.Faces.matchesFace_of_finiteDimensional F hbij hlip C hC hfin (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C) rfl
  have hyu : ‖y‖ • u = y := by
    rw [hu, smul_smul, mul_inv_cancel₀ hypos.ne', one_smul]
  have hymem : y ∈ F '' (‖y‖ • (Metric.closedBall (0 : X) 1 ∩ F ⁻¹' C)) := by
    rw [hcone ‖y‖ ⟨norm_nonneg y, hyle⟩]
    have h := Set.smul_mem_smul_set (a := ‖y‖) huC
    rwa [hyu] at h
  obtain ⟨z, hz, hFz⟩ := hymem
  obtain ⟨d, hd, rfl⟩ := Set.mem_smul_set.mp hz
  have hdS : d ∈ Metric.sphere (0 : X) 1 := hD.2.2.1 hd
  have hdn : ‖d‖ = 1 := by simpa using hdS
  have hzn : ‖‖y‖ • d‖ = ‖y‖ := by rw [norm_smul, norm_norm, hdn, mul_one]
  have hzB : ‖y‖ • d ∈ Metric.closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, hzn]; exact hyle
  have hzx : ‖y‖ • d = x := hbij.injOn hzB hxB (by rw [hFz])
  have : ‖y‖ = 1 := by rw [← hzn, hzx, hxn]
  simpa using this

end Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (F : X → Y)
    (hbij : Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hcover : ∀ y ∈ Metric.sphere (0 : Y) 1, ∃ C : Set Y,
      IsSphereFace C ∧ FiniteDimensional ℝ (vectorSpan ℝ C) ∧ y ∈ C) :
    ∃ T : X ≃ₗᵢ[ℝ] Y, Set.EqOn F T (Metric.closedBall (0 : X) 1) := by
  have h0X : (0 : X) ∈ Metric.closedBall (0 : X) 1 := Metric.mem_closedBall_self zero_le_one
  have h0Y : (0 : Y) ∈ Metric.closedBall (0 : Y) 1 := Metric.mem_closedBall_self zero_le_one
  rcases subsingleton_or_nontrivial X with hX | hX <;>
    rcases subsingleton_or_nontrivial Y with hY | hY
  · exact ⟨Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered.lieOfSubsingleton X Y, fun _ _ => Subsingleton.elim _ _⟩
  · exfalso
    obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (E := Y) (x := 0) (r := 1)).mpr zero_le_one
    obtain ⟨x, hx, hFx⟩ := hbij.surjOn (Metric.sphere_subset_closedBall hy)
    obtain ⟨x', hx', hFx'⟩ := hbij.surjOn h0Y
    have hyy : y = 0 := by rw [← hFx, ← hFx', Subsingleton.elim x x']
    have hyn : ‖y‖ = 1 := by simpa using hy
    rw [hyy, norm_zero] at hyn
    exact zero_ne_one hyn
  · exfalso
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := X) (x := 0) (r := 1)).mpr zero_le_one
    have hx0 : x = 0 :=
      hbij.injOn (Metric.sphere_subset_closedBall hx) h0X (Subsingleton.elim _ _)
    have hxn : ‖x‖ = 1 := by simpa using hx
    rw [hx0, norm_zero] at hxn
    exact zero_ne_one hxn
  · exact Plasticity.U10 F hbij.mapsTo hbij.surjOn hlip
      (Sol_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered.maps_sphere F hbij hlip hcover)
