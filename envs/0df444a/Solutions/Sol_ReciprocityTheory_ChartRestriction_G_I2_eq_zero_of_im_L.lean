-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.eq_zero_of_im_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:27.401907+00:00
-- url     : https://prove2.me/submissions/d9def715-7b45-4e20-b02c-3d062cc5fe8a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, (Hf y a).im = 0) : a = 0 := by
  have hH : ∀ y, Hf y a = inner ℂ a y := fun y => by
    simp [Hf, PiLp.inner_apply, mul_comm]
  have hf : (Complex.imLm.comp ((innerₛₗ ℂ a).restrictScalars ℝ) : Vsp X.dim →ₗ[ℝ] ℝ) = 0 :=
    X.b.ext fun i => by
      simpa [← hH] using h (X.b i) (Submodule.subset_span ⟨i, rfl⟩)
  have h0 : (inner ℂ a ((Complex.I : ℂ) • a)).im = 0 := by
    have := LinearMap.congr_fun hf ((Complex.I : ℂ) • a)
    first
      | exact this
      | (simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, innerₛₗ_apply,
          LinearMap.zero_apply] at this
         exact this)
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
  have h2 : ‖a‖ ^ 2 = 0 := by
    have h3 : (Complex.I * ((‖a‖ : ℂ) ^ 2)).im = ‖a‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [← h3]
    exact h0
  simpa using h2
end ReciprocityTheory.ChartRestriction.G.I2
