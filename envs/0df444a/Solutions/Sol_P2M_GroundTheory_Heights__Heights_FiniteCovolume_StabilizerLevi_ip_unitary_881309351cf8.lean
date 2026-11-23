-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_unitary_881309351cf8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:10.592815+00:00
-- url     : https://prove2.me/submissions/1213f581-bfb4-46ce-977a-fb65ea5659e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_sesq_mul_064c0e5bfacf

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
theorem _root_.solution {H g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (a b : ι → ℂ) :
    star (g *ᵥ a) ⬝ᵥ (H *ᵥ (g *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by
  rw [← sesq_mul, hg]
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
