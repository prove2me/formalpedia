-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_zero_of_hForm_9f2691cc4673
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:29.150935+00:00
-- url     : https://prove2.me/submissions/b966169c-c493-45a3-a68d-31e6c284d0ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable (H : Matrix ι ι ℂ)
variable [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {H : Matrix ι ι ℂ} (hd : IsUnit H.det) {u : ι → ℂ}
    (hu : ∀ z, hForm H u z = 0) : u = 0 := by
  have h1 : star u ᵥ* H = 0 := by
    ext j
    have := hu (Pi.single j 1)
    rw [hForm, dotProduct_mulVec, dotProduct_single_one] at this
    exact this
  have h2 : star u = 0 := by
    have := congrArg (fun r => r ᵥ* H⁻¹) h1
    simpa [vecMul_vecMul, mul_nonsing_inv H hd] using this
  simpa using congrArg star h2
end GroundTheory.Heights₂.Heights.FiniteCovolume
