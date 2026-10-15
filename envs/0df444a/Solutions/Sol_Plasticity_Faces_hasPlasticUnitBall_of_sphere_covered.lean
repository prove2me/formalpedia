-- Prove2me | solution 1 for Plasticity.Faces.hasPlasticUnitBall_of_sphere_covered
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T00:47:27.476853+00:00
-- url     : https://prove2.me/submissions/a13704a0-cc33-4f2a-b0b3-10cd1ac1737c

import Definitions.Def_Plasticity_Basic
import Definitions.Def_Plasticity_Faces
import Theorems.Thm_Plasticity_Faces_exists_linearIsometryEquiv_of_sphere_covered

open Plasticity

namespace Sol_Plasticity_Faces_hasPlasticUnitBall_of_sphere_covered

/-- A two-space conclusion for maps of `X` that are bijective and 1-Lipschitz on the closed unit
ball yields plasticity of the unit ball as a metric space. -/
theorem plastic_of_maps {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : ∀ F : X → X, Set.BijOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1) →
      LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1) →
      ∃ T : X ≃ₗᵢ[ℝ] X, Set.EqOn F T (Metric.closedBall (0 : X) 1)) :
    HasPlasticUnitBall X := by
  classical
  intro f hf hbij
  let B := Metric.closedBall (0 : X) 1
  let F : X → X := fun x => if h : x ∈ B then ((f ⟨x, h⟩ : B) : X) else 0
  have hFx : ∀ x (h : x ∈ B), F x = ((f ⟨x, h⟩ : B) : X) := by
    intro x h; simp only [F, dif_pos h]
  have hF : ∀ a : B, F a = f a := by
    intro a; rw [hFx a a.2]
  have hbijF : Set.BijOn F B B := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx; rw [hFx x hx]; exact (f _).2
    · intro x hx y hy hxy
      rw [hFx x hx, hFx y hy] at hxy
      have := hbij.1 (Subtype.ext hxy)
      exact congrArg Subtype.val this
    · intro y hy
      obtain ⟨a, ha⟩ := hbij.2 ⟨y, hy⟩
      refine ⟨a, a.2, ?_⟩
      rw [hF, ha]
  have hlipF : LipschitzOnWith 1 F B := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hFx x hx, hFx y hy]
    exact hf.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨T, hT⟩ := H F hbijF hlipF
  rw [isometry_iff_dist_eq]
  intro a b
  change dist ((f a : B) : X) ((f b : B) : X) = dist (a : X) (b : X)
  rw [← hF, ← hF, hT a.2, hT b.2, LinearIsometryEquiv.dist_map]

end Sol_Plasticity_Faces_hasPlasticUnitBall_of_sphere_covered

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hcover : ∀ x ∈ Metric.sphere (0 : X) 1, ∃ C : Set X,
      IsSphereFace C ∧ FiniteDimensional ℝ (vectorSpan ℝ C) ∧ x ∈ C) :
    HasPlasticUnitBall X :=
  Sol_Plasticity_Faces_hasPlasticUnitBall_of_sphere_covered.plastic_of_maps fun F hbij hlip =>
    Plasticity.Faces.exists_linearIsometryEquiv_of_sphere_covered F hbij hlip hcover
