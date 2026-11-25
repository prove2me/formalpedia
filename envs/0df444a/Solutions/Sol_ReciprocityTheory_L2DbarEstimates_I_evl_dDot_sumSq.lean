-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_dDot_sumSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:48:37.567974+00:00
-- url     : https://prove2.me/submissions/d551da79-6be6-4b7b-b6d7-3831c7e07d89

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_smoothR_sumSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


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
    dDot n z (fun y => ((∑ i ∈ s, ‖g i y‖ ^ 2 : ℝ) : ℂ)) x ξ =
      ∑ i ∈ s, conj (g i x) * dDot n z (g i) x ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evl_dDot_zero n z x ξ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, Complex.ofReal_add]
    rw [evl_dDot_add n z _ _ (SmoothR.ckR n z 1 _ (Smooth.normSq n z _ (Holo.smooth n z _ (hg a))))
      (SmoothR.ckR n z 1 _ (evl_smoothR_sumSq n z s g hg)) x ξ,
      evl_dDot_normSq n z (g a) (hg a) x ξ, ih]
end ReciprocityTheory.L2DbarEstimates.I
