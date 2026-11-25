-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_zero_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:06.695852+00:00
-- url     : https://prove2.me/submissions/b0a05632-032f-43a4-b6fe-f8a8b4e84dd5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Cutoff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_tsupport_d_subset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_tsupport_db_subset


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ) (x : M)
    (hx : x ∉ tsupport (fun y => (η y : ℂ))) :
    η x = 0 ∧ (∀ j, d n z j (fun y => (η y : ℂ)) x = 0) ∧
      (∀ j, db n z j (fun y => (η y : ℂ)) x = 0) := by
  refine ⟨?_, fun j => ?_, fun j => ?_⟩
  · have := image_eq_zero_of_notMem_tsupport hx; exact_mod_cast this
  · exact image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_d_subset n z j _ h))
  · exact image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_db_subset n z j _ h))
end ReciprocityTheory.L2DbarEstimates.F
