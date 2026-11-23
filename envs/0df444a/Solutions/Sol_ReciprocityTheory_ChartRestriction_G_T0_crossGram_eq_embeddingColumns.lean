-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.crossGram_eq_embeddingColumns
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:13.512389+00:00
-- url     : https://prove2.me/submissions/5e83ebfa-d1f7-4c87-ac9c-14247fb3898e

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns

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
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (σ : K →+* ℂ) {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramX 1 σ b c = (hBm σ b)ᴴ * hBm σ c := by
  ext i j
  simp [ReciprocityTheory.MultiplicativeHeights.gramX, ReciprocityTheory.MultiplicativeHeights.embVec, hBm, Matrix.mul_apply, dotProduct,
    Matrix.conjTranspose_apply]
end ReciprocityTheory.ChartRestriction.G.T0
