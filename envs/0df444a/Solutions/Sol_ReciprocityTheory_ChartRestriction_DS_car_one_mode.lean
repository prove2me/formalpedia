-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.car_one_mode
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:33.781448+00:00
-- url     : https://prove2.me/submissions/6c82d885-6416-4a1f-8865-741b5e5e5c83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution :
    IsCAR (fun _ _ : Fin 1 => cpOne) (fun _ _ : Fin 1 => cmOne) ∧
      ∀ x y : EuclideanSpace ℂ (Fin 2), inner ℂ (cpOne x) y = inner ℂ x (cmOne y) := by
  refine ⟨fun i a j b => ?_, fun x y => ?_⟩
  · have hi : i = j := Subsingleton.elim _ _
    have ha : a = b := Subsingleton.elim _ _
    subst hi; subst ha
    refine ⟨?_, ?_, ?_⟩ <;> refine LinearMap.ext fun x => ?_ <;> ext k <;> fin_cases k <;>
      simp [cpOne, cmOne, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [cpOne, cmOne, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      PiLp.inner_apply, mul_comm]
end ReciprocityTheory.ChartRestriction.DS
