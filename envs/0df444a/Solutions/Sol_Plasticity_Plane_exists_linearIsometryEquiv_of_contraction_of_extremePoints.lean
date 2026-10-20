-- Prove2me | solution 1 for Plasticity.Plane.exists_linearIsometryEquiv_of_contraction_of_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:45.337589+00:00
-- url     : https://prove2.me/submissions/0c21e824-5273-4dd0-bee6-4fb93d835454

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Sol_Plasticity_Plane_exists_linearIsometryEquiv_of_contraction_of_extremePoints

/-- The image of the closed unit ball under `A` contains the closed unit ball of `W`. -/
theorem closedBall_subset_image {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (A : V →ₗ[ℝ] W) (g : W → V)
    (hg : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      ‖g w‖ ≤ 1 ∧ A (g w) = w) :
    Metric.closedBall (0 : W) 1 ⊆ A '' Metric.closedBall (0 : V) 1 := by
  have hcont : Continuous A := LinearMap.continuous_of_finiteDimensional A
  have hcomp : IsCompact (A '' Metric.closedBall (0 : V) 1) :=
    (isCompact_closedBall (0 : V) 1).image hcont
  have hconv : Convex ℝ (A '' Metric.closedBall (0 : V) 1) :=
    (convex_closedBall (0 : V) 1).linear_image A
  have hext : Set.extremePoints ℝ (Metric.closedBall (0 : W) 1) ⊆
      A '' Metric.closedBall (0 : V) 1 := by
    intro w hw
    obtain ⟨h1, h2⟩ := hg w hw
    exact ⟨g w, by simpa using h1, h2⟩
  rw [← closure_convexHull_extremePoints (isCompact_closedBall (0 : W) 1)
    (convex_closedBall (0 : W) 1)]
  exact closure_minimal (convexHull_min hext hconv) hcomp.isClosed

end Sol_Plasticity_Plane_exists_linearIsometryEquiv_of_contraction_of_extremePoints

open Sol_Plasticity_Plane_exists_linearIsometryEquiv_of_contraction_of_extremePoints in
theorem solution {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (A : V →ₗ[ℝ] W) (hA : ∀ v, ‖A v‖ ≤ ‖v‖) (g : W → V)
    (hg : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      ‖g w‖ ≤ 1 ∧ A (g w) = w) :
    ∃ L : V ≃ₗᵢ[ℝ] W, ∀ v, L v = A v := by
  have hsub := closedBall_subset_image A g hg
  -- surjectivity
  have hsurj : Function.Surjective A := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · exact ⟨0, map_zero A⟩
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    obtain ⟨u, -, hu⟩ := hsub (show ‖w‖⁻¹ • w ∈ Metric.closedBall (0 : W) 1 by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hn.ne'])
    refine ⟨‖w‖ • u, ?_⟩
    rw [map_smul, hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hinj : Function.Injective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  -- norm preservation
  have hnorm : ∀ v, ‖A v‖ = ‖v‖ := by
    intro v
    refine le_antisymm (hA v) ?_
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hAv : A v ≠ 0 := by
      intro h
      exact hv (hinj (h.trans (map_zero A).symm))
    have hn : 0 < ‖A v‖ := norm_pos_iff.mpr hAv
    obtain ⟨u, hu1, hu⟩ := hsub (show ‖A v‖⁻¹ • A v ∈ Metric.closedBall (0 : W) 1 by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hn.ne'])
    have hueq : u = ‖A v‖⁻¹ • v := hinj (by rw [hu, map_smul])
    rw [mem_closedBall_zero_iff, hueq, norm_smul, norm_inv, norm_norm] at hu1
    rwa [inv_mul_le_iff₀ hn, mul_one] at hu1
  exact ⟨⟨LinearEquiv.ofBijective A ⟨hinj, hsurj⟩, hnorm⟩, fun v => rfl⟩
