-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slRest_symm_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:15.306312+00:00
-- url     : https://prove2.me/submissions/e683d715-6294-419f-8fad-51b595ddaf94

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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n)
    {j : Fin k} (h : j ≠ i) : (slRest i).symm (p, r) j = r ⟨j, h⟩ := by
  simp [slRest, Equiv.funSplitAt_symm_apply, h]
end ReciprocityTheory.ChartRestriction.DS
