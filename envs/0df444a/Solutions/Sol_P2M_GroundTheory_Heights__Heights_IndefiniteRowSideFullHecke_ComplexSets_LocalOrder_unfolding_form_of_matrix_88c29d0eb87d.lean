-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalOrder_unfolding_form_of_matrix_88c29d0eb87d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:05.240745+00:00
-- url     : https://prove2.me/submissions/8ce55af7-0d0c-44f7-8186-5bb653a83859

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsLocalBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_UnfoldingFormOfMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace LocalOrder
theorem _root_.solution (hB : BranchesToGoodPosition.Statement)
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.Statement) :
    GroundTheory.Heights₂.Heights.LocalOrder.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  obtain ⟨q, π, U, V, ρ, hg⟩ := hB n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  exact h n d J W u q π U V ρ _ ⟨hJ, hdim⟩ hu hW hg
end LocalOrder
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
