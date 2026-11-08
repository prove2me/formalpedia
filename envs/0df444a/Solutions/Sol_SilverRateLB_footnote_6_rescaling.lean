-- Prove2me | solution 1 for SilverRateLB.footnote_6_rescaling
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:33:01.765947+00:00
-- url     : https://prove2.me/submissions/1696f356-0be7-4131-8719-bf752374a9a8

import Mathlib
import Definitions.Def_SilverRateLB_worstCaseRate

namespace Aux_SilverRateLB_resc
open SilverRateLB

lemma grad_smul {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    gradient (fun y => c * f y) x = c • gradient f x := by
  unfold gradient
  rw [fderiv_const_mul hf c, map_smulₛₗ]
  simp

lemma smooth_smul {d : ℕ} (L c : ℝ) (hc : 0 < c) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : KatyushaNs.IsConvexLSmooth L f) :
    KatyushaNs.IsConvexLSmooth (c * L) (fun x => c * f x) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨h1.smul hc.le, h2.const_mul c, fun x y => ?_⟩
  rw [grad_smul f x (h2 x) c, grad_smul f y (h2 y) c, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h3 x y) hc.le

lemma gd_smul {d : ℕ} (c : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Differentiable ℝ f) :
    ∀ (H : List ℝ) (x₀ : EuclideanSpace ℝ (Fin d)),
      gdRun (fun x => c * f x) H x₀ = gdRun f (H.map (fun h => c * h)) x₀ := by
  intro H
  induction H with
  | nil => intro x₀; rfl
  | cons h H ih =>
    intro x₀
    simp only [gdRun, List.foldl_cons, List.map_cons]
    rw [grad_smul f x₀ (hf x₀) c, smul_smul, mul_comm h c]
    exact ih _

end Aux_SilverRateLB_resc

open SilverRateLB Aux_SilverRateLB_resc in
theorem solution (L : ℝ) (hL : 0 < L) (H : List ℝ) :
    worstCaseRate L H = worstCaseRate 1 (H.map (fun h => L * h)) := by
  unfold worstCaseRate
  apply le_antisymm
  · refine iSup_le fun d => iSup_le fun f => iSup_le fun hf => iSup_le fun xs =>
      iSup_le fun hxs => iSup_le fun x₀ => iSup_le fun hx₀ => ?_
    set g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (1 / L) * f x with hgdef
    have hg : KatyushaNs.IsConvexLSmooth 1 g := by
      have := smooth_smul L (1 / L) (by positivity) f hf
      rwa [one_div_mul_cancel hL.ne'] at this
    have hgxs : ∀ y, g xs ≤ g y := fun y =>
      mul_le_mul_of_nonneg_left (hxs y) (by positivity)
    have hfg : (fun x => L * g x) = f := by
      funext x; simp only [hgdef]; field_simp
    have hgd : gdRun g (H.map (fun h => L * h)) x₀ = gdRun f H x₀ := by
      rw [← gd_smul L g hg.2.1 H x₀, hfg]
    refine le_iSup_of_le d (le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le xs
      (le_iSup_of_le hgxs (le_iSup_of_le x₀ (le_iSup_of_le hx₀ (le_of_eq ?_)))))))
    rw [hgd]
    congr 1
    have hn : 0 < ‖x₀ - xs‖ := norm_pos_iff.2 (sub_ne_zero.2 hx₀)
    simp only [hgdef]
    field_simp
  · refine iSup_le fun d => iSup_le fun g => iSup_le fun hg => iSup_le fun xs =>
      iSup_le fun hxs => iSup_le fun x₀ => iSup_le fun hx₀ => ?_
    set f : EuclideanSpace ℝ (Fin d) → ℝ := fun x => L * g x with hfdef
    have hf : KatyushaNs.IsConvexLSmooth L f := by
      have := smooth_smul 1 L hL g hg
      rwa [mul_one] at this
    have hfxs : ∀ y, f xs ≤ f y := fun y =>
      mul_le_mul_of_nonneg_left (hxs y) hL.le
    have hgd : gdRun f H x₀ = gdRun g (H.map (fun h => L * h)) x₀ :=
      gd_smul L g hg.2.1 H x₀
    refine le_iSup_of_le d (le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le xs
      (le_iSup_of_le hfxs (le_iSup_of_le x₀ (le_iSup_of_le hx₀ (le_of_eq ?_)))))))
    rw [hgd]
    congr 1
    have hn : 0 < ‖x₀ - xs‖ := norm_pos_iff.2 (sub_ne_zero.2 hx₀)
    simp only [hfdef]
    field_simp
