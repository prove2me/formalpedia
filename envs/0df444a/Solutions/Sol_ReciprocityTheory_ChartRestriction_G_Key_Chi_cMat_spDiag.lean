-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat_spDiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:03.691992+00:00
-- url     : https://prove2.me/submissions/f0f498ff-21c9-47f5-9119-020c606309ee

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
theorem _root_.solution {g : ℕ} (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) :
    cMat (spDiag U) = Matrix.fromBlocks ((U : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ))) 0 0
      (((U⁻¹ : (Matrix (Fin g) (Fin g) ℤ)ˣ) : Matrix (Fin g) (Fin g) ℤ).map (fun x : ℤ => (x : ℂ)))ᵀ := by
  simp [cMat, spDiag, Matrix.fromBlocks_map, Matrix.transpose_map]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
