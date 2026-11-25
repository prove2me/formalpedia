-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.symPart_posDef_of_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:30.76234+00:00
-- url     : https://prove2.me/submissions/b1878e7f-a033-459c-90ea-336825f021f3

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_quad_pos_of_sphere
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_symPart_isHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
theorem _root_.solution (A : Matrix ι ι ℝ)
    (h : ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < y ⬝ᵥ ((A + Aᵀ) *ᵥ y)) : (A + Aᵀ).PosDef := by
  exact Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨symPart_isHermitian A, fun x hx => by simpa using quad_pos_of_sphere _ h x hx⟩
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
