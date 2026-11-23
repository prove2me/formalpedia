-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_sesq_mul_064c0e5bfacf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:23.236148+00:00
-- url     : https://prove2.me/submissions/65b8e4ed-6cd9-44f5-b05b-ac2cd1a49f2b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {κ' : Type*} [Fintype κ']
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
theorem _root_.solution (H : Matrix ι ι ℂ) (M : Matrix ι κ ℂ) (N : Matrix ι κ' ℂ) (c : κ → ℂ)
    (d : κ' → ℂ) : star c ⬝ᵥ ((Mᴴ * H * N) *ᵥ d) = star (M *ᵥ c) ⬝ᵥ (H *ᵥ (N *ᵥ d)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
