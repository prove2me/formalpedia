-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.wdenSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:27.065186+00:00
-- url     : https://prove2.me/submissions/cdf881e5-0efd-4975-8bfa-d89761f46b37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution : WdenSuccStatement := by
  intro K _ n t
  unfold wden
  rw [Fin.prod_univ_castSucc]
  have hlast : ∀ j : Fin (n + 1), ¬ (Fin.last n < j) := fun j => not_lt.mpr (Fin.le_last j)
  simp only [hlast, if_false, Finset.prod_const_one, mul_one]
  simp only [Fin.prod_univ_castSucc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, if_true]
  rw [Finset.prod_mul_distrib]
end ReciprocityTheory.ChartRestriction.TR.Weyl
