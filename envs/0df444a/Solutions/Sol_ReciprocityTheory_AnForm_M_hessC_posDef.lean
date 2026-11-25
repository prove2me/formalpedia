-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.hessC_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:32.553429+00:00
-- url     : https://prove2.me/submissions/84b21eff-3de8-41c3-8082-afaedac14e11

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Theorems.Thm_ReciprocityTheory_AnForm_M_re_star_dot_hessC
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_isHermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hpos : ∀ w : Fin D → ℂ, w ≠ 0 → 0 < levi φ z w) : (hessC φ z).PosDef := by
  have hH := ReciprocityTheory.AnForm.A.hessC_isHermitian φ z hφ
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hw : star x ≠ 0 := star_ne_zero.2 hx
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [Complex.lt_def]
  refine ⟨?_, ?_⟩
  · rw [Complex.zero_re, re_star_dot_hessC]
    exact hpos _ hw
  · rw [Complex.zero_im]
    exact him.symm
end ReciprocityTheory.AnForm.M
