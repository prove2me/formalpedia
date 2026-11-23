-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:08.972922+00:00
-- url     : https://prove2.me/submissions/45cea04c-8b19-4f63-b5d4-3678c62fefd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_462e477e9506

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
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {M : Matrix ι ι ℂ} (hM : Mᴴ * H * M = H) (u z : ι → ℂ) :
    hForm H (M *ᵥ u) (M *ᵥ z) = hForm H u z := by
  rw [hForm_mulVec, hM]
end GroundTheory.Heights₂.Heights.FiniteCovolume
