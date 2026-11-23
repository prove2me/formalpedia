-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_debb3da7c3fb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:13.097797+00:00
-- url     : https://prove2.me/submissions/8b91f578-f21f-45dd-87e3-d43733168aaf

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
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (y : ι → ℂ) (s : ℂ) (z : ι → ℂ) :
    heisMat H a y s *ᵥ z = z + hForm H a z • (y + s • a) - hForm H y z • a := by
  simp [heisMat, sub_mulVec, add_mulVec, vecMulVec_mulVec, hForm, dotProduct_mulVec]
end GroundTheory.Heights₂.Heights.FiniteCovolume
