-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_matrix_ext_mulVec_52bd164b4cc0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:12.869824+00:00
-- url     : https://prove2.me/submissions/20e61510-ec26-4281-9437-11c34255a50d

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
theorem _root_.solution {A B : Matrix ι ι ℂ} (h : ∀ z, A *ᵥ z = B *ᵥ z) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this
end GroundTheory.Heights₂.Heights.FiniteCovolume
