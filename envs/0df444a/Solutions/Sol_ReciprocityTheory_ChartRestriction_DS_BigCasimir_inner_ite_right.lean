-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.inner_ite_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:41.996839+00:00
-- url     : https://prove2.me/submissions/94c5ad87-4ab4-4640-a9e6-06cbc4586fbf

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
    inner ℂ x (if p then y else 0) = if p then inner ℂ x y else 0 := by
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
