-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.contDiff_of_contDiffOn_zero_off
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:15.936945+00:00
-- url     : https://prove2.me/submissions/3253509c-44bd-459c-acb5-1a60ae5b8cf6

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
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} {m : WithTop ℕ∞} (hf : ContDiffOn ℝ m f U)
    (h0 : ∀ z ∉ K, f z = 0) : ContDiff ℝ m f := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hz)
  · have hzK : z ∈ Kᶜ := fun h => hz (hKU h)
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isOpen_compl.mem_nhds hzK] with y hy using h0 y hy
end ReciprocityTheory.AnForm.A
