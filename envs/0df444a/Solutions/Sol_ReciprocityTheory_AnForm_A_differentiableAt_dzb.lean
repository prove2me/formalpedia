-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.differentiableAt_dzb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:57.212585+00:00
-- url     : https://prove2.me/submissions/af42bf0b-dc84-460a-9e92-8e71084ac7f7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
variable {D : ℕ} {j : Fin D} {f g : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hf : ContDiffAt ℝ 2 f z) : DifferentiableAt ℝ (dzb j f) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by first | norm_num | simp | rfl)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) z :=
    hd.clm_apply (differentiableAt_const _)
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Complex.I • Pi.single j 1)) z :=
    hd.clm_apply (differentiableAt_const _)
  have h3 : DifferentiableAt ℝ (fun y => Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) z :=
    (differentiableAt_const _).mul h2
  have h4 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single j 1) +
      Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) z := h1.add h3
  have h5 : DifferentiableAt ℝ (fun y => (fderiv ℝ f y (Pi.single j 1) +
      Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) / 2) z := by
    first
      | (exact h4.div_const (2 : ℂ))
      | (simpa only [div_eq_mul_inv] using h4.mul_const (2⁻¹ : ℂ))
      | (fun_prop)
  exact h5
end ReciprocityTheory.AnForm.A
