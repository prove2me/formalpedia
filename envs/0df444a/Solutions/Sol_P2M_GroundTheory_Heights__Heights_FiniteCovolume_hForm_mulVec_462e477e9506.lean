-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_462e477e9506
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:11.331474+00:00
-- url     : https://prove2.me/submissions/f3f3fc20-a1cc-4f95-9ae1-2513fb559b20

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
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (M : Matrix ι ι ℂ) (u z : ι → ℂ) :
    hForm H (M *ᵥ u) (M *ᵥ z) = hForm (Mᴴ * H * M) u z := by
  simp only [hForm]
  rw [star_mulVec, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mul_assoc]
end GroundTheory.Heights₂.Heights.FiniteCovolume
