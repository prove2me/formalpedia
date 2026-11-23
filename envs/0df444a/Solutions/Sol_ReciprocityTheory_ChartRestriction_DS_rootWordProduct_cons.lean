-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rootWordProduct_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:02.99383+00:00
-- url     : https://prove2.me/submissions/a38565e6-25c4-4bd2-9044-93177319e227

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule

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
theorem _root_.solution {k : ℕ} (p : Fin n × Fin n) (κ : Fin k → Fin n × Fin n) :
    word E (Fin.cons p κ : Fin (k + 1) → Fin n × Fin n) = E p.1 p.2 * word E κ := by
  first
  | simp only [word, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]
  | simp [word, List.ofFn_succ]
end ReciprocityTheory.ChartRestriction.DS
