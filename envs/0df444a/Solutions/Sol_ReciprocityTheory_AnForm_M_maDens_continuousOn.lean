-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.maDens_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:16.508266+00:00
-- url     : https://prove2.me/submissions/a9046a82-0a88-4b4d-bdb3-b881bd2400f8

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessC_continuousOn

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
theorem _root_.solution {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (V : Set (Fin D → ℂ))
    (hV : IsOpen V) (hφ : ∀ k, ContDiffOn ℝ 2 (φ k) V) : ContinuousOn (maDens φ) V := by
  have hH : ∀ k, ContinuousOn (hessC (φ k)) V := fun k => hessC_continuousOn (φ k) V hV (hφ k)
  unfold maDens mdisc
  refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn ?_)
  refine continuousOn_const.mul (continuousOn_finset_sum _ fun S _ => continuousOn_const.mul ?_)
  exact (continuous_id.matrix_det).comp_continuousOn (continuousOn_finset_sum _ fun k _ => hH k)
end ReciprocityTheory.AnForm.M
