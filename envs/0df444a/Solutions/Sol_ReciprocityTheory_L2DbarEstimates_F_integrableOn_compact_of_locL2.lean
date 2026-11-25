-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.integrableOn_compact_of_locL2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:59:09.756863+00:00
-- url     : https://prove2.me/submissions/94f8c167-56e1-4986-88a6-20bd117ff30c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_multA_integrable_of_sq

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) [IsFiniteMeasureOnCompacts μ] (u : M → ℂ) (hu : LocalL2Isometry μ u)
    (K : Set M) (hK : IsCompact K) : IntegrableOn u K μ := by
  unfold LocalL2Isometry at hu
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact multA_integrable_of_sq (μ.restrict K) u hu.1.restrict (hu.2 K hK)
end ReciprocityTheory.L2DbarEstimates.F
