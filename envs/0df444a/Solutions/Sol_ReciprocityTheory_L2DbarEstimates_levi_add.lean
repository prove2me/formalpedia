-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.levi_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:01.216332+00:00
-- url     : https://prove2.me/submissions/b0b87f42-5847-46f3-b41c-b60863270856

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_add


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ps : M → ℝ) (hph : CkR n z 2 ph) (hps : CkR n z 2 ps) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ph y + ps y) x ξ = Levi n z ph x ξ + Levi n z ps x ξ := by
  have hph1 : Ck n z 1 (fun y => (ph y : ℂ)) := fun e he => (hph e he).of_le (by norm_num)
  have hps1 : Ck n z 1 (fun y => (ps y : ℂ)) := fun e he => (hps e he).of_le (by norm_num)
  have e1 : (fun y => ((ph y + ps y : ℝ) : ℂ)) = fun y => (ph y : ℂ) + (ps y : ℂ) := by
    funext y; exact Complex.ofReal_add _ _
  have h1 : ∀ k, db n z k (fun y => ((ph y + ps y : ℝ) : ℂ)) =
      fun y => db n z k (fun y => (ph y : ℂ)) y + db n z k (fun y => (ps y : ℂ)) y := by
    intro k; funext y; rw [e1]; exact db_add n z _ _ hph1 hps1 k y
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((ph y + ps y : ℝ) : ℂ))) x =
      d n z j (db n z k (fun y => (ph y : ℂ))) x + d n z j (db n z k (fun y => (ps y : ℂ))) x := by
    intro j k; rw [h1 k]; exact d_add n z _ _ (Ck.db n z 1 k _ hph) (Ck.db n z 1 k _ hps) j x
  simp only [Levi, h2, add_mul, Finset.sum_add_distrib]
end ReciprocityTheory.L2DbarEstimates
