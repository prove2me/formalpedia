-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.chord_to_convex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:26.297899+00:00
-- url     : https://prove2.me/submissions/c4b21302-5320-4964-836d-42515834b2d6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {f : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∀ y ∈ s, x < y → ∀ α β : ℝ, f x ≤ α + β * x → f y ≤ α + β * y →
      ∀ p ∈ Icc x y, f p ≤ α + β * p) : ConvexOn ℝ s f := by
  have key : ∀ x ∈ s, ∀ y ∈ s, x < y → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a * x + b * y) ≤ a * f x + b * f y := by
    intro x hx y hy hxy a b ha hb hab
    have hyx : 0 < y - x := sub_pos.2 hxy
    set β := (f y - f x) / (y - x) with hβdef
    have hβ : β * (y - x) = f y - f x := div_mul_cancel₀ _ hyx.ne'
    have ha' : a = 1 - b := by linarith
    have e1 : a * x + b * y - x = b * (y - x) := by rw [ha']; ring
    have e2 : y - (a * x + b * y) = a * (y - x) := by rw [ha']; ring
    have hp : a * x + b * y ∈ Icc x y :=
      ⟨by nlinarith [mul_nonneg hb hyx.le], by nlinarith [mul_nonneg ha hyx.le]⟩
    have := h x hx y hy hxy (f x - β * x) β (by linarith) (by linarith [hβ]) _ hp
    calc f (a * x + b * y) ≤ f x - β * x + β * (a * x + b * y) := this
      _ = a * f x + b * f y := by rw [ha']; linear_combination b * hβ
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact key x hx y hy hxy a b ha hb hab
  · rw [← add_mul, hab, one_mul, ← add_mul, hab, one_mul]
  · have := key y hy x hx hxy b a hb ha (by linarith)
    rw [add_comm (b * y)] at this
    linarith
end ReciprocityTheory.AnForm.A
