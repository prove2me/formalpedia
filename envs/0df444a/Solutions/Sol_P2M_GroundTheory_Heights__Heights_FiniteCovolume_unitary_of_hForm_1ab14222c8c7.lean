-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_of_hForm_1ab14222c8c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:28:32.866178+00:00
-- url     : https://prove2.me/submissions/e1cc8a6e-9e4e-461d-a4a3-07f3334224e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_462e477e9506
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_single_0a847e972e7f

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
theorem _root_.solution {M : Matrix ι ι ℂ}
    (hM : ∀ u z, hForm H (M *ᵥ u) (M *ᵥ z) = hForm H u z) : Mᴴ * H * M = H := by
  ext i j
  have := hM (Pi.single i 1) (Pi.single j 1)
  rw [hForm_mulVec, hForm_single, hForm_single] at this
  exact this
end GroundTheory.Heights₂.Heights.FiniteCovolume
