-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat_spTransl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:54.720003+00:00
-- url     : https://prove2.me/submissions/9a00b491-e53f-4c54-8285-9be7847f104d

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
theorem _root_.solution {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) :
    cMat (spTransl S) = Matrix.fromBlocks 1 (S.map (fun x : ℤ => (x : ℂ))) 0 1 := by
  simp [cMat, spTransl, Matrix.fromBlocks_map]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
