-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:14.321788+00:00
-- url     : https://prove2.me/submissions/93187ebb-2936-4aa0-9072-2e6aacfc553a

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
variable {K : Type} [Field K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (σ : K →+* ℂ) (b : Fin k → Fin r → K) : (hPm σ b)ᴴ = hPm σ b := by
  simp only [hPm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
end ReciprocityTheory.ChartRestriction.G.T0
