-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.inner_ite_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:19.58773+00:00
-- url     : https://prove2.me/submissions/9bc31fa9-0a0c-44f2-ae45-21e0ec728150

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution (p : Prop) [Decidable p] (x y : M) :
    inner ℂ (if p then x else 0) y = if p then inner ℂ x y else 0 := by
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
