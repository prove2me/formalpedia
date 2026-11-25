-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalOrder_unfolding_matrix_of_form_3208b0564a63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:06.490339+00:00
-- url     : https://prove2.me/submissions/b0312d0d-1e16-4a42-aedc-e5a1802caeb6

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
theorem _root_.solution (hG : GoodPositionToBranches.Statement)
    (h : GroundTheory.Heights₂.Heights.LocalOrder.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.Statement := by
  intro n e J W u p π U V ρ N hJ hu hW hg
  obtain ⟨q, m, γ, ord, hq, hcov, hsl, hdisj, hord, hsum⟩ :=
    hG n e J W u p π U V ρ N hJ hu hW hg
  rw [← hsum]
  exact h n e J W u q m γ ord hJ.isPrime hJ.dim hu hW hq hcov hsl hdisj hord
end LocalOrder
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
