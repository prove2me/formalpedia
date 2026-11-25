-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.J_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:40.805416+00:00
-- url     : https://prove2.me/submissions/4a4e24fa-3129-4708-b4bd-c6176b29430b

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
theorem _root_.solution : J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ = 1 := by

  rw [J_cube, neg_mul, Matrix.J_squared, neg_neg]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
