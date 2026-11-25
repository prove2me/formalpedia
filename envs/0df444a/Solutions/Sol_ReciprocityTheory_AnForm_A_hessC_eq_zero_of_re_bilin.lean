-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_eq_zero_of_re_bilin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:27.442802+00:00
-- url     : https://prove2.me/submissions/77ecc13b-bd82-4cd3-ab2b-63775f10fd4b

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Complex Filter Topology
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (B : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ)
    (hB : ∀ v u, fderiv ℝ (fderiv ℝ φ) z v u = (B v u).re) : hessC φ z = 0 := by
  ext i j
  simp only [hessC, hB, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Matrix.zero_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf
  simp
end ReciprocityTheory.AnForm.A
