-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Key_Chi_blk_conjTranspose___ad3e91286297
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:58.841206+00:00
-- url     : https://prove2.me/submissions/8d24e78e-f14d-4678-8752-c221b06bf086

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
    ((cMat γ).toBlocks₂₁)ᴴ = ((cMat γ).toBlocks₂₁)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, cMat, Matrix.toBlocks₂₁]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
