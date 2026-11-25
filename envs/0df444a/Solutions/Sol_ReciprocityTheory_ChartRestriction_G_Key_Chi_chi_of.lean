-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.chi_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:57:07.796264+00:00
-- url     : https://prove2.me/submissions/95f3ac7b-000a-4948-bf09-5e65cf3937fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiU_closure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_chiAt_of_U


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
theorem _root_.solution (hInv : InversionStatement) (hGen : SpGenStatement) : ChiStatement :=
  fun g γ hγ => chiAt_of_U (chiU_closure hInv (hGen g γ hγ)).2
end ReciprocityTheory.ChartRestriction.G.Key.Chi
