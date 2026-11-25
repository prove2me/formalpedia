-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:19.954914+00:00
-- url     : https://prove2.me/submissions/e526251b-8ac3-432e-9f84-30375c52b173

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_mul_embeddingColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_conjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
variable {K : Type} [Field K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (v : Fin r → ℂ) (y : Fin k → ℂ) : star (hPm σ b *ᵥ v) ⬝ᵥ (hBm σ b *ᵥ y) = 0 := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_embeddingColumns σ hb, Matrix.vecMul_zero, zero_dotProduct]
end ReciprocityTheory.ChartRestriction.G.T0
