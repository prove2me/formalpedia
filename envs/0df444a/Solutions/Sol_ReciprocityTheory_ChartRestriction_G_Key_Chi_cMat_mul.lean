-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:54.076221+00:00
-- url     : https://prove2.me/submissions/4b532ebb-5cf7-486e-afa4-5a3fb9b7a8e7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_InversionStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks

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
theorem _root_.solution {g : ℕ} (γ δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    cMat (γ * δ) = cMat γ * cMat δ := by
  have h : (γ * δ).map (Int.castRingHom ℂ) = γ.map (Int.castRingHom ℂ) * δ.map (Int.castRingHom ℂ) :=
    Matrix.map_mul
  simpa [cMat] using h
end ReciprocityTheory.ChartRestriction.G.Key.Chi
