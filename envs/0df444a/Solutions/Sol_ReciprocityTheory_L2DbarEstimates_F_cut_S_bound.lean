-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_S_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:08:48.835227+00:00
-- url     : https://prove2.me/submissions/2379eb22-32ae-47a0-86c9-a655ae42a114

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_cs
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_norm_d_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ)
    (fx : V n) (x : M) :
    ‖∑ j, d n z j (fun y => (η y : ℂ)) x * fx j‖ ^ 2 ≤ dbarSq n z (fun y => (η y : ℂ)) x * ‖fx‖ ^ 2 := by
  have h := cut_cs n (fun j => d n z j (fun y => (η y : ℂ)) x) (fun j => fx j)
  unfold dbarSq
  rw [EuclideanSpace.norm_sq_eq]
  have he : ∑ j, ‖d n z j (fun y => (η y : ℂ)) x‖ ^ 2 =
      ∑ j, ‖db n z j (fun y => (η y : ℂ)) x‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [cut_norm_d_eq]
  rw [← he]
  exact h
end ReciprocityTheory.L2DbarEstimates.F
