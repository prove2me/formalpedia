-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.cdo_of_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:12:41.756996+00:00
-- url     : https://prove2.me/submissions/12cefcbe-6d1e-4cce-80b3-136f8dd93a1a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    (h : ContDiff ℝ 3 f) : ContDiffOn ℝ ((1 : ℕ) + 2) f U := by
  have e : ((1 : ℕ) : WithTop ℕ∞) + 2 = 3 := by norm_num
  rw [e]; exact h.contDiffOn
end ReciprocityTheory.AnForm.A
