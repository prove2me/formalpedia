-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sphereLogIntegrable_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:50:25.937131+00:00
-- url     : https://prove2.me/submissions/6f59600b-4855-4d47-bd11-28d14c57044c

import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresB
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCores
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSlice_isHomogeneous
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_blockSlice
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockPoly_claim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hSJ : SJStatement) : SphereLogIntegrableStatement := by
  intro B n a f _ hf
  set F : (Fin B → Fin n → ℂ) → ℂ := fun p => eval (fun q => p q.1 q.2) f with hFdef
  have hF : BlockPoly B n a F := by
    refine ⟨(continuous_eval f).comp (continuous_pi fun q =>
      (continuous_apply q.2).comp (continuous_apply q.1)), fun b p => ?_⟩
    exact ⟨_, blockSlice_isHomogeneous hf b p, fun w => (eval_blockSlice f b p w).symm⟩
  by_cases hz : ∃ z0, onSpheres F z0 ≠ 0
  · obtain ⟨z0, hz0⟩ := hz
    exact (blockPoly_claim hSJ n B a F hF z0 hz0).1
  · simp only [not_exists, not_not] at hz
    have : (fun z : BlockSphere B n => Real.log ‖eval (blockPoint z) f‖) = fun _ => 0 := by
      funext z
      have h0 : eval (blockPoint z) f = 0 := hz z
      rw [h0, norm_zero, Real.log_zero]
    rw [this]
    exact integrable_zero _ _ _
end ReciprocityTheory.MultiplicativeHeights
