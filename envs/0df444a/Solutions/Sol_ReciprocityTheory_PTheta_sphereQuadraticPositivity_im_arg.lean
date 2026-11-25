-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.im_arg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:59:34.87994+00:00
-- url     : https://prove2.me/submissions/da927abf-3ea0-487e-ad35-b9140288fcbe

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_shiftVec_eq
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_im_ofReal_dot
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_im_mulVec_ofReal

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
theorem _root_.solution (a b : ι → ℝ) (z : ι → ℂ) (τ : Matrix ι ι ℂ) (l : ι → ℤ) :
    (shiftVec a l ⬝ᵥ (τ *ᵥ shiftVec a l) / 2 + shiftVec a l ⬝ᵥ (z + ofRealVec b)).im =
      (fun i => (l i : ℝ) + a i) ⬝ᵥ (τ.map Complex.im *ᵥ (fun i => (l i : ℝ) + a i)) / 2 +
        (fun i => (l i : ℝ) + a i) ⬝ᵥ (fun i => (z i).im) := by
  rw [shiftVec_eq, Complex.add_im, Complex.div_ofNat_im, im_ofReal_dot, im_mulVec_ofReal,
    im_ofReal_dot]
  congr 2
  funext i
  simp [ofRealVec]
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
