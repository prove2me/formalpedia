-- Prove2me | solution 1 for PositivityTheory.CW.NoncommutativeSwapSum.nc_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:52.435333+00:00
-- url     : https://prove2.me/submissions/9fb43fb2-0012-43eb-ad8f-616c652d4133

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthPolynomialOperator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.NoncommutativeSwapSum
namespace PositivityTheory.CW.NoncommutativeSwapSum
theorem _root_.solution {n : ℕ} {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p.swap = ∑ p ∈ nc ε, f p := by
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_ <;> simp [nc, ne_comm]
end PositivityTheory.CW.NoncommutativeSwapSum
