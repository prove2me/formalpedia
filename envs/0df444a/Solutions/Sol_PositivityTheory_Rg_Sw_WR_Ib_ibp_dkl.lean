-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.ibp_dkl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:41.705562+00:00
-- url     : https://prove2.me/submissions/83f02b10-42f5-459d-b148-d34f9813a028

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_lf_re_im
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_sum_vkl
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_dkl_swap
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_integrable_mul_chr
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_ibp_dir

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
theorem _root_.solution {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgi : Integrable g) (k l : Fin n)
    (h1 : Integrable (Dkl k l g)) (h2 : Integrable (Dkl l k g)) (t : ℝ) (β : E n) :
    ∫ y, Dkl k l g y * chr t β y = -((-(Complex.I * t)) * herm β k l) * ∫ y, g y * chr t β y := by
  set u : E n := fun a b => (vkl k l a b).re
  set w : E n := fun a b => (vkl k l a b).im
  have hre : (fun y => fderiv ℝ g y u) = fun y => (Dkl k l g y + Dkl l k g y) / 2 := by
    funext y; rw [dkl_swap g k l y]; simp only [Dkl, dirC, u, w]; ring
  have him : (fun y => fderiv ℝ g y w) = fun y => (Dkl k l g y - Dkl l k g y) / (2 * Complex.I) := by
    funext y; rw [dkl_swap g k l y]; simp only [Dkl, dirC, u, w]; field_simp; ring
  have iu : Integrable fun y => fderiv ℝ g y u := by rw [hre]; exact (h1.add h2).div_const _
  have iw : Integrable fun y => fderiv ℝ g y w := by rw [him]; exact (h1.sub h2).div_const _
  have hcont := hg.continuous
  have hcu : Continuous fun y => fderiv ℝ g y u :=
    ((contDiff_infty_iff_fderiv.mp hg).2.continuous).clm_apply continuous_const
  have hcw : Continuous fun y => fderiv ℝ g y w :=
    ((contDiff_infty_iff_fderiv.mp hg).2.continuous).clm_apply continuous_const
  have eD : (fun y => Dkl k l g y * chr t β y) =
      fun y => fderiv ℝ g y u * chr t β y + Complex.I * (fderiv ℝ g y w * chr t β y) := by
    funext y; simp only [Dkl, dirC, u, w]; ring
  rw [eD, integral_add (integrable_mul_chr iu hcu t β) ((integrable_mul_chr iw hcw t β).const_mul _),
    integral_const_mul, ibp_dir hg hgi u iu t β, ibp_dir hg hgi w iw t β]
  have h := lf_re_im t β (vkl k l)
  rw [sum_vkl] at h
  linear_combination (-(∫ y, g y * chr t β y)) * h
end PositivityTheory.Rg.Sw.WR.Ib
