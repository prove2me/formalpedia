-- Prove2me | solution 1 for SoficGroups.ejTwoProjection_norm_sq_sum_le_of_angle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/5d849738-61b4-4f91-a5d9-72bacac6fa87

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejStarProjection_re_inner
import Theorems.Thm_SoficGroups_ejStarProjection_mem_inf_orthogonal

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c)
    (hangle : ∀ (u v : H),
      u ∈ U → u ∈ (U ⊓ V)ᗮ →
      v ∈ V → v ∈ (U ⊓ V)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (w : H) (hw : w ∈ (U ⊓ V)ᗮ) :
    ‖U.starProjection w‖ ^ 2 + ‖V.starProjection w‖ ^ 2 ≤
      (1 + c) * ‖w‖ ^ 2 := by
  let u : H := U.starProjection w
  let v : H := V.starProjection w
  have hu : u ∈ U := Submodule.starProjection_apply_mem U w
  have hv : v ∈ V := Submodule.starProjection_apply_mem V w
  have huorth : u ∈ (U ⊓ V)ᗮ :=
    ejStarProjection_mem_inf_orthogonal U V w hw
  have hvorth : v ∈ (U ⊓ V)ᗮ := by
    have h := ejStarProjection_mem_inf_orthogonal V U w (by
      simpa [inf_comm] using hw)
    simpa [inf_comm] using h
  have hre : RCLike.re (inner ℂ u v) ≤ c * ‖u‖ * ‖v‖ :=
    (RCLike.re_le_norm (inner ℂ u v)).trans
      (hangle u v hu huorth hv hvorth)
  have hsum :
      ‖u + v‖ ^ 2 ≤
        (1 + c) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    rw [norm_add_sq (𝕜 := ℂ)]
    nlinarith [mul_nonneg hc (sq_nonneg (‖u‖ - ‖v‖))]
  have huinner :
      (inner ℂ (U.starProjection w) w).re =
        ‖U.starProjection w‖ ^ 2 := by
    change RCLike.re (inner ℂ (U.starProjection w) w) = _
    exact ejStarProjection_re_inner U w
  have hvinner :
      (inner ℂ (V.starProjection w) w).re =
        ‖V.starProjection w‖ ^ 2 := by
    change RCLike.re (inner ℂ (V.starProjection w) w) = _
    exact ejStarProjection_re_inner V w
  have hlinear :
      ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ ‖u + v‖ * ‖w‖ := by
    calc
      ‖u‖ ^ 2 + ‖v‖ ^ 2 =
          RCLike.re (inner ℂ (u + v) w) := by
        dsimp [u, v]
        simp only [inner_add_left, Complex.add_re]
        rw [huinner, hvinner]
      _ ≤ ‖inner ℂ (u + v) w‖ :=
        RCLike.re_le_norm _
      _ ≤ ‖u + v‖ * ‖w‖ :=
        norm_inner_le_norm _ _
  have hsq :
      (‖u‖ ^ 2 + ‖v‖ ^ 2) ^ 2 ≤
        (‖u + v‖ * ‖w‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hlinear
  have hcancel :
      (‖u‖ ^ 2 + ‖v‖ ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤
        ((1 + c) * ‖w‖ ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    calc
      _ = (‖u‖ ^ 2 + ‖v‖ ^ 2) ^ 2 := by ring
      _ ≤ (‖u + v‖ * ‖w‖) ^ 2 := hsq
      _ = ‖u + v‖ ^ 2 * ‖w‖ ^ 2 := by ring
      _ ≤ ((1 + c) * (‖u‖ ^ 2 + ‖v‖ ^ 2)) *
          ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsum (sq_nonneg ‖w‖)
      _ = ((1 + c) * ‖w‖ ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) := by ring
  change ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ (1 + c) * ‖w‖ ^ 2
  by_cases hz : ‖u‖ ^ 2 + ‖v‖ ^ 2 = 0
  · rw [hz]
    positivity
  · have hpos : 0 < ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      _ ≤ ((1 + c) * ‖w‖ ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) := hcancel
      _ = (‖u‖ ^ 2 + ‖v‖ ^ 2) *
          ((1 + c) * ‖w‖ ^ 2) := by ring
end SoficGroups
