-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___779a257255c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:50.975999+00:00
-- url     : https://prove2.me/submissions/3a8ffdb4-24c4-4a0b-8084-6824d81158ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_Blocks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm

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
theorem _root_.solution {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    ((cMat γ).toBlocks₁₂)ᴴ = ((cMat γ).toBlocks₁₂)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, cMat, Matrix.toBlocks₁₂]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
