-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:18.020037+00:00
-- url     : https://prove2.me/submissions/e6d4362d-73b0-4636-a15e-c49894f744eb

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
theorem _root_.solution {D : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin D → E → Matrix (Fin D) (Fin D) ℂ) {s : Set E} {m : WithTop ℕ∞}
    (hA : ∀ k i j, ContDiffOn ℝ m (fun z => A k z i j) s) :
    ContDiffOn ℝ m (fun z => mdisc (fun k => A k z)) s := by
  simp only [mdisc, Matrix.det_apply', Matrix.sum_apply]
  refine contDiffOn_const.mul (ContDiffOn.sum fun S _ => contDiffOn_const.mul
    (ContDiffOn.sum fun σ _ => contDiffOn_const.mul
      (contDiffOn_prod fun i _ => ContDiffOn.sum fun k _ => hA k _ _)))
end ReciprocityTheory.AnForm.A
