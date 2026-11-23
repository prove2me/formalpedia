-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.levi_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:20.513152+00:00
-- url     : https://prove2.me/submissions/13d03cd6-ecba-4cf7-b1cb-c4a49b79d743

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_const_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_const_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) (ph : M → ℝ) (hph : CkR n z 2 ph) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => c * ph y) x ξ = (c : ℂ) * Levi n z ph x ξ := by
  have hph1 : Ck n z 1 (fun y => (ph y : ℂ)) := fun e he => (hph e he).of_le (by norm_num)
  have e1 : (fun y => ((c * ph y : ℝ) : ℂ)) = fun y => (c : ℂ) * (ph y : ℂ) := by
    funext y; exact Complex.ofReal_mul _ _
  have h1 : ∀ k, db n z k (fun y => ((c * ph y : ℝ) : ℂ)) =
      fun y => (c : ℂ) * db n z k (fun y => (ph y : ℂ)) y := by
    intro k; funext y; rw [e1]; exact db_const_mul n z _ _ hph1 k y
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((c * ph y : ℝ) : ℂ))) x =
      (c : ℂ) * d n z j (db n z k (fun y => (ph y : ℂ))) x := by
    intro j k; rw [h1 k]; exact d_const_mul n z _ _ (Ck.db n z 1 k _ hph) j x
  simp only [Levi, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring
end ReciprocityTheory.L2DbarEstimates
