-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_right_bdac4345363f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:45.239822+00:00
-- url     : https://prove2.me/submissions/3739d64c-ba90-49bb-9263-6cb39a0bad89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_swap_b2eefeb2a9e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_B_left_c137c8023bfd

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
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ} {X Y : ι → ℂ}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
theorem _root_.solution (hH : Hᴴ = H) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) (c : κ → ℂ) :
    star X ⬝ᵥ (H *ᵥ (B *ᵥ c)) = 0 := by
  rw [ip_swap hH, ip_B_left hBX, star_zero]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
