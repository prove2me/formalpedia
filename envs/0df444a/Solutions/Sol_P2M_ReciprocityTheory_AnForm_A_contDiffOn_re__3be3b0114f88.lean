-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_contDiffOn_re__3be3b0114f88
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:58.20565+00:00
-- url     : https://prove2.me/submissions/586526fc-2f58-44e7-aa8d-c75c5f71b78d

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ}
    {s : Set E} {m : WithTop ℕ∞} (h : ContDiffOn ℝ m g s) :
    ContDiffOn ℝ m (fun z => (g z).re) s :=
  Complex.reCLM.contDiff.comp_contDiffOn h
end ReciprocityTheory.AnForm.A
