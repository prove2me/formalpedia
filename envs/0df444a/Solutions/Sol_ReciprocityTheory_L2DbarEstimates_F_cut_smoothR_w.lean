-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_smoothR_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:03.193337+00:00
-- url     : https://prove2.me/submissions/b61bf263-1210-4516-8857-675423ad3923

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ψ : M → ℝ)
    (hph : SmoothR n z ph) (hψ : SmoothR n z ψ) :
    SmoothR n z (w1 ph ψ) ∧ SmoothR n z (w2 ph ψ) := by
  have h1 : ∀ c : ℝ, SmoothR n z (fun x => ph x + (fun _ => c) x * ψ x) := fun c =>
    SmoothR.add n z _ _ hph (SmoothR.mul n z _ _ (Smooth.const n z ((c : ℝ) : ℂ)) hψ)
  have e1 : w1 ph ψ = fun x => ph x + (fun _ => (-2 : ℝ)) x * ψ x := by
    funext x; simp only [w1]; ring
  have e2 : w2 ph ψ = fun x => ph x + (fun _ => (-1 : ℝ)) x * ψ x := by
    funext x; simp only [w2]; ring
  rw [e1, e2]; exact ⟨h1 _, h1 _⟩
end ReciprocityTheory.L2DbarEstimates.F
