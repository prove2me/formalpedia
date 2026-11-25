-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_levi_sumSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:48:11.846981+00:00
-- url     : https://prove2.me/submissions/f1266d06-20bc-4a38-a881-869e78f5098e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_levi_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_smoothR_sumSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (g : ι → M → ℂ) (hg : ∀ i, Holo n z (g i)) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ∑ i ∈ s, ‖g i y‖ ^ 2) x ξ =
      ((∑ i ∈ s, ‖dDot n z (g i) x ξ‖ ^ 2 : ℝ) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evl_levi_zero n z x ξ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [levi_add n z (fun y => ‖g a y‖ ^ 2) (fun y => ∑ i ∈ s, ‖g i y‖ ^ 2)
      (SmoothR.ckR n z 2 _ (Smooth.normSq n z _ (Holo.smooth n z _ (hg a))))
      (SmoothR.ckR n z 2 _ (evl_smoothR_sumSq n z s g hg)) x ξ,
      levi_normSq n z (g a) (hg a) x ξ, ih]
    push_cast; ring
end ReciprocityTheory.L2DbarEstimates.I
