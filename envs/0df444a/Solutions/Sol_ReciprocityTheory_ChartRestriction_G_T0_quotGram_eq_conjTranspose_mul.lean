-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.quotGram_eq_conjTranspose_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:22.218465+00:00
-- url     : https://prove2.me/submissions/8fcad7d6-a741-4881-a463-7abd1728f113

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_crossGram_eq_embeddingColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gramMatrix_eq_embeddingColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_conjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {m : ℕ} (c : Fin m → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hPm σ b * hBm σ c)ᴴ * (hPm σ b * hBm σ c) := by
  have e1 : ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hBm σ c)ᴴ * hPm σ b * hBm σ c := by
    simp only [ReciprocityTheory.MultiplicativeHeights.quotGramC, crossGram_eq_embeddingColumns, gramMatrix_eq_embeddingColumns, hPm, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e1]
  simp only [conjTranspose_mul, orthogonalProjector_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hPm σ b) (hPm σ b), orthogonalProjector_mul_self σ hb]
end ReciprocityTheory.ChartRestriction.G.T0
