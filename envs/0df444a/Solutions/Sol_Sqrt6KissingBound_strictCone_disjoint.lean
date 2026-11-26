-- Prove2me | solution 1 for Sqrt6KissingBound.strictCone_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:19:33.338948+00:00
-- url     : https://prove2.me/submissions/551308f3-7d6f-43bc-9919-b787128b771f

import Mathlib
import Definitions.Def_Sqrt6KissingBound_Geometry
import Theorems.Thm_Sqrt6KissingBound_sqrt3_sq_geom

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace Sqrt6KissingBound
theorem _root_.solution {x z : E}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hxz : inner ℝ x z ≤ (1 : ℝ) / 2) :
    Disjoint (strictCone x) (strictCone z) := by
  rw [Set.disjoint_left]
  intro y hyx hyz
  change (s3 / 2) * ‖y‖ < inner ℝ x y at hyx
  change (s3 / 2) * ‖y‖ < inner ℝ z y at hyz
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    simp at hyx
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  let u : E := NormedSpace.normalize y
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    exact norm_normalize hy0
  let a : ℝ := inner ℝ x u
  let b : ℝ := inner ℝ z u
  have ha : s3 / 2 < a := by
    have hdiv : s3 / 2 < inner ℝ x y / ‖y‖ :=
      (lt_div_iff₀ hny).2 hyx
    change s3 / 2 < inner ℝ x (NormedSpace.normalize y)
    rw [NormedSpace.normalize, real_inner_smul_right]
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hb : s3 / 2 < b := by
    have hdiv : s3 / 2 < inner ℝ z y / ‖y‖ :=
      (lt_div_iff₀ hny).2 hyz
    change s3 / 2 < inner ℝ z (NormedSpace.normalize y)
    rw [NormedSpace.normalize, real_inner_smul_right]
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hc0 : 0 ≤ s3 / 2 := by positivity
  have ha0 : 0 ≤ a := hc0.trans ha.le
  have hb0 : 0 ≤ b := hc0.trans hb.le
  let p : E := x - a • u
  let q : E := z - b • u
  have hp_sq : ‖p‖ ^ 2 = 1 - a ^ 2 := by
    dsimp [p]
    rw [norm_sub_sq_real, norm_smul, hx, hu, Real.norm_eq_abs,
      abs_of_nonneg ha0, real_inner_smul_right]
    change 1 ^ 2 - 2 * (a * a) + (a * 1) ^ 2 = 1 - a ^ 2
    ring
  have hq_sq : ‖q‖ ^ 2 = 1 - b ^ 2 := by
    dsimp [q]
    rw [norm_sub_sq_real, norm_smul, hz, hu, Real.norm_eq_abs,
      abs_of_nonneg hb0, real_inner_smul_right]
    change 1 ^ 2 - 2 * (b * b) + (b * 1) ^ 2 = 1 - b ^ 2
    ring
  have ha_sq : (3 : ℝ) / 4 < a ^ 2 := by
    have hpow : (s3 / 2) ^ 2 < a ^ 2 := (sq_lt_sq₀ hc0 ha0).2 ha
    nlinarith [sqrt3_sq_geom]
  have hb_sq : (3 : ℝ) / 4 < b ^ 2 := by
    have hpow : (s3 / 2) ^ 2 < b ^ 2 := (sq_lt_sq₀ hc0 hb0).2 hb
    nlinarith [sqrt3_sq_geom]
  have hp : ‖p‖ < (1 : ℝ) / 2 := by
    have hn : 0 ≤ ‖p‖ := norm_nonneg p
    nlinarith
  have hq : ‖q‖ < (1 : ℝ) / 2 := by
    have hn : 0 ≤ ‖q‖ := norm_nonneg q
    nlinarith
  have hab : (3 : ℝ) / 4 < a * b := by
    have hc : 0 < s3 / 2 := by positivity
    have h₁ : (s3 / 2) * (s3 / 2) < a * (s3 / 2) :=
      mul_lt_mul_of_pos_right ha hc
    have h₂ : a * (s3 / 2) < a * b :=
      mul_lt_mul_of_pos_left hb (hc.trans ha)
    nlinarith [sqrt3_sq_geom]
  have hprod : ‖p‖ * ‖q‖ < (1 : ℝ) / 4 := by
    calc
      ‖p‖ * ‖q‖ ≤ ‖p‖ * ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hq.le (norm_nonneg p)
      _ < ((1 : ℝ) / 2) * ((1 : ℝ) / 2) :=
        mul_lt_mul_of_pos_right hp (by norm_num)
      _ = (1 : ℝ) / 4 := by norm_num
  have hpq : -(1 : ℝ) / 4 < inner ℝ p q := by
    have habs : |inner ℝ p q| ≤ ‖p‖ * ‖q‖ := abs_real_inner_le_norm p q
    have hlower : -(‖p‖ * ‖q‖) ≤ inner ℝ p q := (abs_le.mp habs).1
    linarith
  have hpq_eq : inner ℝ p q = inner ℝ x z - a * b := by
    simp only [p, q, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow]
    have huz : inner ℝ u z = b := by
      rw [real_inner_comm]
    have hxu : inner ℝ x u = a := rfl
    rw [huz, hxu]
    ring
  have hdecomp : inner ℝ x z = a * b + inner ℝ p q := by
    rw [hpq_eq]
    ring
  rw [hdecomp] at hxz
  linarith
end Sqrt6KissingBound
