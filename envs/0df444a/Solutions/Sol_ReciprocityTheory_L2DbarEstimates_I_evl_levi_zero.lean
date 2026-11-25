-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_levi_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:28.920622+00:00
-- url     : https://prove2.me/submissions/55acc1b1-15b2-4c10-8d56-38d55de51d8f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_const
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_const


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (x : M)
    (ξ : Fin n → ℂ) : Levi n z (fun _ => (0 : ℝ)) x ξ = 0 := by
  have h : ∀ k, db n z k (fun _ => ((0 : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
    intro k; funext y; exact db_const n z _ k y
  unfold Levi
  simp only [h, d_const, zero_mul, Finset.sum_const_zero]
end ReciprocityTheory.L2DbarEstimates.I
