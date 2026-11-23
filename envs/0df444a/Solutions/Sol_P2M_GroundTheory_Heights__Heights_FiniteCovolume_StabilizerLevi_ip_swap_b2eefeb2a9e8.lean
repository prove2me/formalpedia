-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_swap_b2eefeb2a9e8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:10.548743+00:00
-- url     : https://prove2.me/submissions/92f3ff9a-bbc5-4d64-9720-3f93f6e94d50

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
theorem _root_.solution {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (a b : ι → ℂ) :
    star b ⬝ᵥ (H *ᵥ a) = star (star a ⬝ᵥ (H *ᵥ b)) := by
  rw [← star_dotProduct, star_mulVec, ← dotProduct_mulVec, hH]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
