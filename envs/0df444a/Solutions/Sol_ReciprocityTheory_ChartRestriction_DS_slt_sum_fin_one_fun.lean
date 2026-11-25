-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slt_sum_fin_one_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:55.112546+00:00
-- url     : https://prove2.me/submissions/9968a4d3-7170-4b0e-a2ba-dcd7a164d336

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
theorem _root_.solution {β : Type*} [AddCommMonoid β] (f : (Fin n × Fin n) → β) :
    ∑ ι : Fin 1 → Fin n × Fin n, f (ι 0) = ∑ p, f p := by
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun ι => by simp)
end ReciprocityTheory.ChartRestriction.DS
