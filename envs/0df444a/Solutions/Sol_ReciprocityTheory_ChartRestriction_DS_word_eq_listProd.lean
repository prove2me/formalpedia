-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.word_eq_listProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:25.385285+00:00
-- url     : https://prove2.me/submissions/2f95b0bd-b2ff-42ec-8572-cfad701d27d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm

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
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {k : ℕ} (κ : Fin k → Fin n × Fin n) :
    word E κ = ((List.ofFn κ).map fun p => E p.1 p.2).prod := by
  rw [word, List.map_ofFn]
  rfl
end ReciprocityTheory.ChartRestriction.DS
