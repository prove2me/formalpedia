-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.ibp_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:19.227841+00:00
-- url     : https://prove2.me/submissions/5f7d51d9-5804-45b7-878c-0753743908ac

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_fderiv_chr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_differentiable_chr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_integrable_mul_chr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgi : Integrable g) (w : E n)
    (hgw : Integrable fun y => fderiv ℝ g y w) (t : ℝ) (β : E n) :
    ∫ y, fderiv ℝ g y w * chr t β y = -(lf t β w) * ∫ y, g y * chr t β y := by
  have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hcont : Continuous g := hg.continuous
  have hcw : Continuous fun y => fderiv ℝ g y w :=
    ((contDiff_infty_iff_fderiv.mp hg).2.continuous).clm_apply continuous_const
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := g) (g := chr t β) (v := w)
    (integrable_mul_chr hgw hcw t β)
    (by
      have : (fun y => g y * fderiv ℝ (chr t β) y w) = fun y => (g y * chr t β y) * lf t β w := by
        funext y; rw [fderiv_chr]; ring
      rw [this]
      exact (integrable_mul_chr hgi hcont t β).mul_const _)
    (integrable_mul_chr hgi hcont t β)
    (fun x _ => hdiff x) (fun x _ => differentiable_chr t β x)
  have : (fun y => g y * fderiv ℝ (chr t β) y w) = fun y => (g y * chr t β y) * lf t β w := by
    funext y; rw [fderiv_chr]; ring
  rw [this, integral_mul_const] at H
  linear_combination H
end PositivityTheory.Rg.Sw.WR.Ib
