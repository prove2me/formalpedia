-- Prove2me | solution 1 for P2M_LinearProgrammingBound__5ed74557e9ce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/9b3f57ab-d790-4d2c-a5d6-20e93da4c71e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicSpherePacking_orbit_cardinality_eq_bounded_representatives
import Theorems.Thm_SchwartzMap_lattice_covolume_eq_coordinate_determinant
import Theorems.Thm_test_function_positive_at_origin
import Theorems.Thm_packing_bound_complete_estimate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking MeasureTheory Complex Real Bornology Module
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
variable {P : PeriodicSpherePacking d} (hP : P.separation = 1) [Nonempty P.centers]
variable {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
variable (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
include d f hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ P hP D hD_isBounded
  hD_unique_covers
theorem _root_.solution (hd : 0 < d) :
  P.upperPackingDensity ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
  volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  classical
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hfunction : 0 < (f 0).re :=
    test_function_positive_at_origin hne_zero hReal hRealFourier hCohnElkies₂
  have hball :
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
    (EuclideanSpace.euclidean_ball_volume_positive (0 : EuclideanSpace ℝ (Fin d))
      (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have hball_inv :
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 : ℝ)⁻¹) ≠ 0 := by
    simpa only [one_div] using hball
  by_cases hfourier_zero : (𝓕 f 0).re = 0
  · simp [hfourier_zero, div_eq_mul_inv,
      (Real.toNNReal_pos.mpr hfunction).ne', hball_inv]
  · have hfourier : 0 < (𝓕 f 0).re :=
      lt_of_le_of_ne (hCohnElkies₂ 0) (Ne.symm hfourier_zero)
    have hcount_nat : 0 < P.centerOrbitCardinality := by
      unfold PeriodicSpherePacking.centerOrbitCardinality
      exact Fintype.card_pos_iff.mpr
        ⟨Quotient.mk _ (Classical.choice (inferInstance : Nonempty P.centers))⟩
    have hcount :
        0 < (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) := by
      rw [← P.orbit_cardinality_eq_bounded_representatives hd hD_isBounded
        hD_unique_covers]
      exact_mod_cast hcount_nat
    have hcovolume : 0 < ZLattice.covolume P.lattice volume := by
      rw [SchwartzMap.lattice_covolume_eq_coordinate_determinant]
      apply abs_pos.mpr
      intro hdet
      let e := SchwartzMap.latticeCoordinateEquiv P.lattice
      have hcomp : e.toLinearMap * e.symm.toLinearMap = 1 := by
        ext x
        simp
      have hdetcomp := congrArg
        (LinearMap.det :
          ((EuclideanSpace ℝ (Fin d)) →ₗ[ℝ]
            (EuclideanSpace ℝ (Fin d))) →* ℝ) hcomp
      simp [map_mul, hdet, e] at hdetcomp
    have hestimate :=
      packing_bound_complete_estimate (f := f) hRealFourier hCohnElkies₁
        hCohnElkies₂ hP hD_isBounded hD_unique_covers hd
    have hscaled :
        (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) ^ 2 *
            (𝓕 f 0).re ≤
          ((P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) *
            (f 0).re) * ZLattice.covolume P.lattice volume :=
      (div_le_iff₀ hcovolume).mp hestimate
    have hcancel :
        (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) *
            (𝓕 f 0).re ≤
          (f 0).re * ZLattice.covolume P.lattice volume := by
      apply le_of_mul_le_mul_left _ hcount
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hreal :
        (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) /
            ZLattice.covolume P.lattice volume ≤
          (f 0).re / (𝓕 f 0).re :=
      (div_le_div_iff₀ hcovolume hfourier).mpr hcancel
    have hnonnegative := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos hcovolume,
      ENNReal.ofReal_div_of_pos hfourier] at hnonnegative
    have hnonnegative' :
      (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ≥0∞) /
          (ZLattice.covolume P.lattice volume).toNNReal ≤
        (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal := by
      simpa [ENNReal.ofReal] using hnonnegative
    rw [P.density_eq_numReps_mul_volume_ball_div_covolume hd, hP,
      P.orbit_cardinality_eq_bounded_representatives hd hD_isBounded
        hD_unique_covers]
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_left hnonnegative'
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)))
