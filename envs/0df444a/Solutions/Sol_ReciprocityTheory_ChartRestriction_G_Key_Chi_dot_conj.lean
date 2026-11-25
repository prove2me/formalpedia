-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.dot_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:26:02.675082+00:00
-- url     : https://prove2.me/submissions/6b20c1a2-573b-44b0-a187-72c9c8558af4

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
theorem _root_.solution {g : ℕ} (P Y : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    z ⬝ᵥ ((P * Y * Pᵀ) *ᵥ z) = (Pᵀ *ᵥ z) ⬝ᵥ (Y *ᵥ (Pᵀ *ᵥ z)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_transpose]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
