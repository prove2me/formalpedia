-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.hessC_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:20.42203+00:00
-- url     : https://prove2.me/submissions/82888bdc-199e-47c1-874f-6e31f439b87a

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
theorem _root_.solution {D : ℕ} {v : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (hz : z ∉ tsupport v) : hessC v z = 0 := by
  have h1 : v =ᶠ[𝓝 z] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).1 hz
  have h2 : fderiv ℝ (fderiv ℝ v) z = 0 := by
    rw [h1.fderiv.fderiv_eq]
    simp
  ext i j
  simp [hessC, h2]
end ReciprocityTheory.AnForm.A
