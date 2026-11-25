-- Prove2me | solution 1 for PositivityTheory.CW.GrowthPolynomialOperator.sum_nc_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:22:27.93634+00:00
-- url     : https://prove2.me/submissions/4ce6eaf0-6b08-4c25-933b-4f25c969329d

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthOfBasic

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
open PositivityTheory.CW.GrowthPolynomialOperator
variable {n : ℕ}
namespace PositivityTheory.CW.GrowthPolynomialOperator
theorem _root_.solution {β : Type*} [AddCommMonoid β] (ε : Fin n → Bool) (g : Fin n × Fin n → β) :
    ∑ p ∈ nc ε, g p.swap = ∑ p ∈ nc ε, g p := by
  apply Finset.sum_nbij' Prod.swap Prod.swap <;> simp [nc, ne_comm]
end PositivityTheory.CW.GrowthPolynomialOperator
