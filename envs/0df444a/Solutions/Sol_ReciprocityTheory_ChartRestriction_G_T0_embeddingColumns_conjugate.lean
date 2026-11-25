-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.embeddingColumns_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:29.363656+00:00
-- url     : https://prove2.me/submissions/74cf09ae-435e-4304-8086-f22c24b72c7c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate

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
theorem _root_.solution (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    hBm (conjugate σ) b = (hBm σ b).map (starRingEnd ℂ) := by
  ext l j
  simp [hBm, NumberField.ComplexEmbedding.conjugate_coe_eq]
end ReciprocityTheory.ChartRestriction.G.T0
