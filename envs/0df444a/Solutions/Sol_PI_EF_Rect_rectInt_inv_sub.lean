-- Prove2me | solution 1 for PI.EF.Rect.rectInt_inv_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:46:50.78941+00:00
-- url     : https://prove2.me/submissions/33521cef-03bf-4e12-985d-0627c3cf2d28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_hint_of_hasDerivAt
import Theorems.Thm_PI_EF_Rect_vint_of_hasDerivAt
import Theorems.Thm_PI_EF_Rect_hseg_mem_bdry_bot
import Theorems.Thm_PI_EF_Rect_hseg_mem_bdry_top
import Theorems.Thm_PI_EF_Rect_vseg_mem_bdry_left
import Theorems.Thm_PI_EF_Rect_vseg_mem_bdry_right
import Theorems.Thm_PI_EF_Rect_ne_of_mem_bdry_of_mem_open
import Theorems.Thm_PI_EF_Rect_log_sub_log_neg_of_im_pos
import Theorems.Thm_PI_EF_Rect_log_neg_sub_log_of_im_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real
namespace PI.EF.Rect
theorem _root_.solution {z w p : ℂ} (hp : p ∈ rectOpen z w) :
    rectInt (fun s => (s - p)⁻¹) z w = 2 * π * I := by
  obtain ⟨h1, h2, h3, h4⟩ := id hp
  have hcont : ∀ s ∈ rectBdry z w, ContinuousAt (fun s => (s - p)⁻¹) s := fun s hs =>
    ContinuousAt.inv₀ (by fun_prop) (sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp))
  have hL : ∀ s, s - p ∈ slitPlane → HasDerivAt (fun s => Complex.log (s - p)) ((s - p)⁻¹) s := by
    intro s hs
    simpa using ((hasDerivAt_id s).sub_const p).clog hs
  have hM : ∀ s, p - s ∈ slitPlane → HasDerivAt (fun s => Complex.log (p - s)) ((s - p)⁻¹) s := by
    intro s hs
    convert ((hasDerivAt_id s).const_sub p).clog hs using 1
    simp only [id_eq]
    rw [neg_div, ← div_neg, neg_sub, one_div]
    rfl
  unfold rectInt
  rw [hint_of_hasDerivAt (F := fun s => Complex.log (s - p)) (f := fun s => (s - p)⁻¹)
      (a₁ := z.re) (a₂ := w.re) (b := z.im)
      (fun x _ => hL _ (mem_slitPlane_iff.2 (Or.inr (by intro h; simp at h; linarith))))
      (fun x hx => hcont _ (hseg_mem_bdry_bot hx)),
    hint_of_hasDerivAt (F := fun s => Complex.log (s - p)) (f := fun s => (s - p)⁻¹)
      (a₁ := z.re) (a₂ := w.re) (b := w.im)
      (fun x _ => hL _ (mem_slitPlane_iff.2 (Or.inr (by intro h; simp at h; linarith))))
      (fun x hx => hcont _ (hseg_mem_bdry_top hx)),
    vint_of_hasDerivAt (F := fun s => Complex.log (s - p)) (f := fun s => (s - p)⁻¹)
      (a := w.re) (b₁ := z.im) (b₂ := w.im)
      (fun y _ => hL _ (mem_slitPlane_iff.2 (Or.inl (by simp; linarith))))
      (fun y hy => hcont _ (vseg_mem_bdry_right hy)),
    vint_of_hasDerivAt (F := fun s => Complex.log (p - s)) (f := fun s => (s - p)⁻¹)
      (a := z.re) (b₁ := z.im) (b₂ := w.im)
      (fun y _ => hM _ (mem_slitPlane_iff.2 (Or.inl (by simp; linarith))))
      (fun y hy => hcont _ (vseg_mem_bdry_left hy))]
  have e1 := log_sub_log_neg_of_im_pos (a := (z.re : ℂ) + w.im * I - p) (by simp; linarith)
  have e2 := log_neg_sub_log_of_im_neg (b := (z.re : ℂ) + z.im * I - p) (by simp; linarith)
  rw [neg_sub] at e1 e2
  beta_reduce
  linear_combination e1 + e2
end PI.EF.Rect
