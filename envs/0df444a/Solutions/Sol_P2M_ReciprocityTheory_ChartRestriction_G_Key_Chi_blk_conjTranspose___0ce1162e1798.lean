-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___0ce1162e1798
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:47.169956+00:00
-- url     : https://prove2.me/submissions/11127d93-b6c8-4d75-ba62-d32a71b37ef0

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
    ((cMat γ).toBlocks₁₁)ᴴ = ((cMat γ).toBlocks₁₁)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, cMat, Matrix.toBlocks₁₁]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
