-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.orthogonalProjector_mulVec_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:45:42.568073+00:00
-- url     : https://prove2.me/submissions/233e2f82-6b91-45ae-8bd8-fb0529bcd519

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_orthogonalProjector_conjugate

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
    (x : Fin r → K) :
    (hPm (conjugate σ) b *ᵥ fun l => (conjugate σ) (x l)) = star (hPm σ b *ᵥ fun l => σ (x l)) := by
  rw [orthogonalProjector_conjugate σ hb]
  ext i
  simp [Matrix.mulVec, dotProduct, NumberField.ComplexEmbedding.conjugate_coe_eq, map_sum,
    mul_comm]
end ReciprocityTheory.ChartRestriction.G.T0
