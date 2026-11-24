-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:48.95488+00:00
-- url     : https://prove2.me/submissions/21e4d8a4-b9e9-4324-92db-70343f34ec78

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere

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
theorem _root_.solution (A : Matrix ι ι ℝ) (r : ℝ) (x : ι → ℝ) :
    (r • x) ⬝ᵥ (A *ᵥ (r • x)) = r ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
