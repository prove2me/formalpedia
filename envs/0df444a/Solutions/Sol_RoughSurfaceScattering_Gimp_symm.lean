-- Prove2me | solution 1 for RoughSurfaceScattering.Gimp_symm
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T11:33:44.501812+00:00
-- url     : https://prove2.me/submissions/ca3778a8-bad0-4cfb-8c11-a72039ad5921

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory
open RoughSurfaceScattering

/-- `Φ_k` depends only on the distance. -/
lemma Phi_congr (k : ℝ) (x y x' y' : R2) (h : ‖x - y‖ = ‖x' - y'‖) : Phi k x y = Phi k x' y' := by
  simp only [Phi, h]

/-- `P_k^±(z)` depends only on `|z|` and `z₂`. -/
lemma Pimp_congr (k σ : ℝ) (z z' : R2) (hn : ‖z‖ = ‖z'‖) (h1 : z 1 = z' 1) :
    Pimp k σ z = Pimp k σ z' := by
  simp only [Pimp, hn, h1]

lemma refl_sub_coords (a : ℝ) (x y : R2) :
    (x - refl a y) 0 = x 0 - y 0 ∧ (x - refl a y) 1 = x 1 + y 1 - 2 * a := by
  simp only [RoughSurfaceScattering.refl, pt, PiLp.sub_apply]
  constructor <;> simp <;> ring

lemma norm_sub_refl (a : ℝ) (x y : R2) : ‖x - refl a y‖ = ‖y - refl a x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  obtain ⟨h0, h1⟩ := refl_sub_coords a x y
  obtain ⟨h0', h1'⟩ := refl_sub_coords a y x
  rw [h0, h1, h0', h1']
  congr 1
  simp only [Real.norm_eq_abs, sq_abs]
  ring

theorem solution (k a σ : ℝ) (x y : R2) : Gimp k a σ x y = Gimp k a σ y x := by
  unfold Gimp
  rw [Phi_congr k x y y x (norm_sub_rev x y),
    Phi_congr k x (refl a y) y (refl a x) (norm_sub_refl a x y),
    Pimp_congr k σ (x - refl a y) (y - refl a x) (norm_sub_refl a x y)
      (by rw [(refl_sub_coords a x y).2, (refl_sub_coords a y x).2]; ring)]
