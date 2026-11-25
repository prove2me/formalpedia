-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.kPsi_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:32:50.560014+00:00
-- url     : https://prove2.me/submissions/87d462b2-5dc5-4472-8be4-95729c175426

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_KPsiHasCompactSupport
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (ph : M → ℝ) (φ : M → ℂ) (hφ : IsTest n z φ) (j k : Fin n) :
    HasCompactSupport (kPsi n z ph φ j k) := by
  refine hφ.2.mono' fun x hx => ?_
  by_contra hnot
  have hj : db n z j φ x = 0 := by
    by_contra h
    exact hnot (tsupport_db_subset n z j φ (subset_tsupport _ h))
  have hk : db n z k φ x = 0 := by
    by_contra h
    exact hnot (tsupport_db_subset n z k φ (subset_tsupport _ h))
  exact hx (by simp [kPsi, hj, hk])
end ReciprocityTheory.L2DbarEstimates.F
