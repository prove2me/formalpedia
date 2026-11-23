-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.db_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:05.848673+00:00
-- url     : https://prove2.me/submissions/2367e542-c333-4303-9908-7703d5fa4d36

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_conj
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
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n) (x : M) :
    db n z j (fun y => (ph y : ℂ)) x = (starRingEnd ℂ) (d n z j (fun y => (ph y : ℂ)) x) := by
  have h1 := db_conj n z (fun y => (ph y : ℂ)) j x
  simpa using h1
end ReciprocityTheory.L2DbarEstimates
