-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spLow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:50.947197+00:00
-- url     : https://prove2.me/submissions/207a9786-8dcf-4489-9341-f7ab3d468aa5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_J_cube

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
theorem _root_.solution (S : Matrix (Fin g) (Fin g) ℤ) :
    spLow S = J (Fin g) ℤ * spTransl (-S) * (J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ) := by

  rw [J_cube]
  unfold spLow spTransl
  rw [Matrix.J, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply]
  simp
end ReciprocityTheory.ChartRestriction.G.Key.Chi
