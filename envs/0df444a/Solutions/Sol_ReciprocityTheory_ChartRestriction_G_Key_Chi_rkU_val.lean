-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.rkU_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:02.295648+00:00
-- url     : https://prove2.me/submissions/dab4ef77-a0c6-4954-909d-7c4892f5a2d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol

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
theorem _root_.solution (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) :
    ((rkU u v h : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ) = 1 + vecMulVec u v := rfl
end ReciprocityTheory.ChartRestriction.G.Key.Chi
