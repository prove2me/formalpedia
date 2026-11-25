-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.one_eq_spTransl_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:03.673091+00:00
-- url     : https://prove2.me/submissions/3ab22f22-e6a1-42e6-9103-ac9b28777418

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (g : ℕ) :
    (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = spTransl 0 := by
  exact Matrix.fromBlocks_one.symm
end ReciprocityTheory.ChartRestriction.G.Key.Chi
