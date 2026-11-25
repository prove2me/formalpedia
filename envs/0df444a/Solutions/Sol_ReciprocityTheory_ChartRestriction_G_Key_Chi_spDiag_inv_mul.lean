-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spDiag_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:17:05.256336+00:00
-- url     : https://prove2.me/submissions/dbd9bc76-4b4d-4839-a594-b98b03d3672b

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
theorem _root_.solution (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : spDiag U⁻¹ * spDiag U = 1 := by

  simp [spDiag, fromBlocks_multiply, ← Matrix.transpose_mul, fromBlocks_one]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
