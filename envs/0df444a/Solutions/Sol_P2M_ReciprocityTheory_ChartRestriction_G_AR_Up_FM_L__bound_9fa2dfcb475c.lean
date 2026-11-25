-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_L__bound_9fa2dfcb475c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:35:43.293617+00:00
-- url     : https://prove2.me/submissions/aba138ed-b5b1-4756-b33e-e55d172626c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_Umat_upper
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI__0_det_6ea7967b69c5
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI__0_upper_9db1d5f297f4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_UF_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_gram_rmul_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_gram_upper_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_sgn_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM
theorem _root_.solution {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {R0 : ℝ}
    (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0) {p : Frame X.Ψ r} (hp : p ∈ X.dom)
    {y : UpI X.Ψ r → ℂ} (hy : ∀ τ b, y (dI τ b) ≠ 0) (hx : rmul p (UF X y) ∈ C) (i : UpI X.Ψ r) :
    ‖Lβ (β0 X p) y i‖ ≤ R0 := by
  set x := rmul p (UF X y) with hxdef
  set τ := i.1.1
  have hxd : x ∈ X.dom := hCd hx
  have h1 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X p τ * mat (UF X y) τ) := gram_rmul_eq X hp τ
  let one : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  have hone' : rmul x one = x := by
    funext τ'
    show (mat x τ' * (1 : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = x τ'
    rw [Matrix.mul_one]; rfl
  have h2 : gram τ.1 X.Gm (mat x τ) = gramT X (β0 X x τ * mat one τ) := by
    have := gram_rmul_eq X hxd τ (b := one)
    rwa [hone'] at this
  have hone : mat one τ = 1 := rfl
  rw [hone, Matrix.mul_one] at h2
  have hU : mat (UF X y) τ = Umat y τ := rfl
  rw [hU] at h1
  have hUd : (Umat y τ).det ≠ 0 := ((UF_mem X hy) τ).1
  obtain ⟨D, hD, heq⟩ := gram_upper_unique (ε := fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (fun a => sgn_mul_self X.p0 a) (β0_upper X hxd τ) ((β0_upper X hp τ).mul (Umat_upper X y τ))
    (β0_det X hxd τ) (by rw [Matrix.det_mul]; exact mul_ne_zero (β0_det X hp τ) hUd)
    (by have := h1.symm.trans h2; simpa only [gramT, Jd] using this)
  have hval : Lβ (β0 X p) y i = (β0 X p τ * Umat y τ) i.1.2.1 i.1.2.2 := rfl
  rw [hval, heq, Matrix.diagonal_mul, norm_mul, hD, one_mul]
  exact hR0 x hx τ _ _
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
