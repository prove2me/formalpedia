-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spTransl_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:30.352848+00:00
-- url     : https://prove2.me/submissions/a0ced755-b55e-4b9c-8d52-f3bb2993b519

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase

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
theorem _root_.solution (S : Matrix (Fin g) (Fin g) ℤ) : spTransl (-S) * spTransl S = 1 := by

  simp [spTransl, fromBlocks_multiply, fromBlocks_one]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
