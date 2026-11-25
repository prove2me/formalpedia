-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.update_eq_slRest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:32.412029+00:00
-- url     : https://prove2.me/submissions/fa4660f7-e8f8-412f-99ab-33547368c446

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (q : Fin n × Fin n) :
    Function.update κ i q = (slRest i).symm (q, (slRest i κ).2) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [slRest, Equiv.funSplitAt_symm_apply]
  · simp [slRest, Equiv.funSplitAt_symm_apply, Equiv.funSplitAt_apply, h]
end ReciprocityTheory.ChartRestriction.DS
