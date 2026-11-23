-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.compactSpace_KG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:23.65846+00:00
-- url     : https://prove2.me/submissions/2fdac3f2-6b93-4716-a461-6c498702e9a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFactsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Theorems.Thm_UpperTheory_Reformulated_B_Qk16_isClosedEmbedding_toM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) : CompactSpace (KG ε) := by
  have hc : IsCompact (Kset ε) := by
    have hsub : Kset ε ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
        (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) := by
      intro g hg i _ j _
      simpa [Metric.mem_closedBall, dist_zero_right] using entry_norm_bound_of_unitary hg.1 i j
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_Kset ε) hsub
  have hK : IsCompact ((KG ε : Set (UJ ε))) :=
    (isClosedEmbedding_toM ε).isCompact_preimage hc
  exact isCompact_iff_compactSpace.mp hK
end ReciprocityTheory.ChartRestriction.DS.S7
