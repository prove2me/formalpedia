-- Prove2me | solution 1 for SoficGroups.ejTwoResidual_spectral_gap_of_angle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/1eb948f2-d35a-4e32-bcab-1243572c2dec

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejTwoResidualEnergy_ge_of_angle
import Theorems.Thm_SoficGroups_ejTwoResidual_sum_re_inner

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
    [(U ⊓ V).HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hangle : ∀ (u v : H),
      u ∈ U → u ∈ (U ⊓ V)ᗮ →
      v ∈ V → v ∈ (U ⊓ V)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (x : H) :
    (1 - c) *
        (‖ejResidualProjection U x‖ ^ 2 +
          ‖ejResidualProjection V x‖ ^ 2) ≤
      ‖ejResidualProjection U x +
        ejResidualProjection V x‖ ^ 2 := by
  let q : H := (U ⊓ V).starProjection x
  let w : H := x - q
  have hw : w ∈ (U ⊓ V)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  have hq : q ∈ U ⊓ V :=
    Submodule.starProjection_apply_mem (U ⊓ V) x
  have hqU : ejResidualProjection U q = 0 := by
    rw [ejResidualProjection_apply,
      Submodule.starProjection_eq_self_iff.mpr hq.1, sub_self]
  have hqV : ejResidualProjection V q = 0 := by
    rw [ejResidualProjection_apply,
      Submodule.starProjection_eq_self_iff.mpr hq.2, sub_self]
  have hwU : ejResidualProjection U w =
      ejResidualProjection U x := by
    dsimp [w]
    rw [map_sub, hqU, sub_zero]
  have hwV : ejResidualProjection V w =
      ejResidualProjection V x := by
    dsimp [w]
    rw [map_sub, hqV, sub_zero]
  let e : ℝ :=
    ‖ejResidualProjection U w‖ ^ 2 +
      ‖ejResidualProjection V w‖ ^ 2
  let z : H :=
    ejResidualProjection U w + ejResidualProjection V w
  have he : 0 ≤ e := by
    dsimp [e]
    positivity
  have hcoercive : (1 - c) * ‖w‖ ^ 2 ≤ e :=
    ejTwoResidualEnergy_ge_of_angle U V c hc hangle w hw
  have hlinear : e ≤ ‖z‖ * ‖w‖ := by
    calc
      e = RCLike.re (inner ℂ z w) :=
        (ejTwoResidual_sum_re_inner U V w).symm
      _ ≤ ‖inner ℂ z w‖ := RCLike.re_le_norm _
      _ ≤ ‖z‖ * ‖w‖ := norm_inner_le_norm _ _
  have hsq : e ^ 2 ≤ (‖z‖ * ‖w‖) ^ 2 :=
    (sq_le_sq₀ he (by positivity)).mpr hlinear
  have hgap : (1 - c) * e ≤ ‖z‖ ^ 2 := by
    by_cases hz : e = 0
    · rw [hz, mul_zero]
      positivity
    · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hepos).mp
      calc
        e * ((1 - c) * e) = (1 - c) * e ^ 2 := by ring
        _ ≤ (1 - c) * (‖z‖ * ‖w‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr hc')
        _ = ‖z‖ ^ 2 * ((1 - c) * ‖w‖ ^ 2) := by ring
        _ ≤ ‖z‖ ^ 2 * e :=
          mul_le_mul_of_nonneg_left hcoercive (sq_nonneg ‖z‖)
        _ = e * ‖z‖ ^ 2 := by ring
  change (1 - c) * e ≤ ‖z‖ ^ 2 at hgap
  dsimp [e, z] at hgap
  rw [hwU, hwV] at hgap
  exact hgap
end SoficGroups
