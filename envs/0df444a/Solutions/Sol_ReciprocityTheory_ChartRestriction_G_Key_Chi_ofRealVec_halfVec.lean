-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.ofRealVec_halfVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:55.408961+00:00
-- url     : https://prove2.me/submissions/4eb902f6-3237-44cb-abbe-3f53f43ef2f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OfRealVecHalfVec

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
theorem _root_.solution {g : ℕ} (n : Fin g → ℤ) :
    ofRealVec (halfVec n) = (1 / 2 : ℂ) • ofIntVec n := by
  funext i
  simp only [ofRealVec, halfVec, ofIntVec, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.Key.Chi
