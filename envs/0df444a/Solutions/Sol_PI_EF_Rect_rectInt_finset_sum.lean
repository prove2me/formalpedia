-- Prove2me | solution 1 for PI.EF.Rect.rectInt_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:44.226997+00:00
-- url     : https://prove2.me/submissions/974497f4-8409-44b0-9ad7-d054ccd6a773

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
import Theorems.Thm_PI_EF_Rect_rectInt_add
import Theorems.Thm_PI_EF_Rect_rectInt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real
namespace PI.EF.Rect
theorem _root_.solution {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (hF : ∀ i ∈ S, ContinuousOn (F i) (rectBdry z w)) :
    rectInt (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, rectInt (F i) z w := by
  classical
  revert hF
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact rectInt_zero z w
  · intro a S ha ih hF
    simp only [Finset.sum_insert ha]
    rw [rectInt_add (hF a (Finset.mem_insert_self a S))
      (continuousOn_finsetSum _ fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]
end PI.EF.Rect
