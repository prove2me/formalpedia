-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:04.108158+00:00
-- url     : https://prove2.me/submissions/80181daa-c338-4463-b58a-bbc251c0cf2a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd

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
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
namespace ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
theorem _root_.solution {n : ℕ} (H : Fin n × Fin 2 → ℂ) :
    ∑ p : Fin (n * 2), H (finProdFinEquiv.symm p) = ∑ j, (H (j, 0) + H (j, 1)) := by
  rw [Equiv.sum_comp finProdFinEquiv.symm H, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]
end ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
