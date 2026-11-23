-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.J_cube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:03.700462+00:00
-- url     : https://prove2.me/submissions/298b3378-1f4d-4c00-a5f3-b62dbb760b66

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
theorem _root_.solution : J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ = -J (Fin g) ℤ := by

  rw [Matrix.J_squared, neg_mul, one_mul]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
