-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.sum_eJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:34.714717+00:00
-- url     : https://prove2.me/submissions/5338dd9b-d973-433d-b215-86778cb63813

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eJ_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (j i : Fin g) (x : Fin g → ℤ) :
    ∑ l, eJ j i l * x l = if i = j then x j else 0 := by
  simp only [eJ_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Ne.symm h, h]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
