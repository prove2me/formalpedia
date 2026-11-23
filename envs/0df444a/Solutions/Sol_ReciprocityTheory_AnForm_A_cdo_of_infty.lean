-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.cdo_of_infty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:15.685606+00:00
-- url     : https://prove2.me/submissions/da85e95e-c5e8-4e75-8a5e-537340d8b39c

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
    (h : ContDiffOn ℝ ∞ f U) (m : ℕ) : ContDiffOn ℝ (m + 2) f U := by
  exact_mod_cast contDiffOn_infty.1 h (m + 2)
end ReciprocityTheory.AnForm.A
