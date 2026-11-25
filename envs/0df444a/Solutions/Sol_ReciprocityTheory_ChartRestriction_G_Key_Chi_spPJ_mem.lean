-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spPJ_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:57.739216+00:00
-- url     : https://prove2.me/submissions/e0d37892-c2ba-4c7f-88a1-142a0c4ab110

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spLow_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_eJ_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spPJ_eq

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
theorem _root_.solution (j : Fin g) : spPJ j ∈ spH g := by

  have hE := eJ_symm j
  have hE' : (-eJ j).IsSymm := by
    unfold Matrix.IsSymm at hE ⊢
    rw [Matrix.transpose_neg, hE]
  rw [spPJ_eq]
  exact mul_mem (mul_mem (spTransl_mem hE) (spLow_mem hE')) (spTransl_mem hE)
end ReciprocityTheory.ChartRestriction.G.Key.Chi
