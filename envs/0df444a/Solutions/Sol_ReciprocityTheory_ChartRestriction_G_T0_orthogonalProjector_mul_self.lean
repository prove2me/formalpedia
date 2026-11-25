-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:27.216491+00:00
-- url     : https://prove2.me/submissions/01e3c924-a5a9-4e4c-b834-d5cb91a177db

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulEmbeddingColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_conjTranspose_mul_orthogonalProjector

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
theorem _root_.solution (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm σ b * hPm σ b = hPm σ b := by
  have h := conjTranspose_mul_orthogonalProjector σ hb
  calc hPm σ b * hPm σ b
      = (1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ) * hPm σ b := rfl
    _ = hPm σ b - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * ((hBm σ b)ᴴ * hPm σ b) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = hPm σ b := by rw [h, Matrix.mul_zero, sub_zero]
end ReciprocityTheory.ChartRestriction.G.T0
