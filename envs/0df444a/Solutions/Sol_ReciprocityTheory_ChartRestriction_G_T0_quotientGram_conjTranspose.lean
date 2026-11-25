-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.quotientGram_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:34.414633+00:00
-- url     : https://prove2.me/submissions/f13f2f08-31dc-4c9b-8778-91e60ff9a577

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_crossGram_eq_embeddingColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gramMatrix_eq_embeddingColumns


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder Kronecker
variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) : (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c)ᴴ = ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c := by
  unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
  simp only [gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.T0
