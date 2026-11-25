-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ext_sesq_f168d8060b14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:14.693635+00:00
-- url     : https://prove2.me/submissions/34d798dc-dc15-48a2-b588-aefa32792324

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
theorem _root_.solution {M N : Matrix κ κ ℂ}
    (h : ∀ c d : κ → ℂ, star c ⬝ᵥ (M *ᵥ d) = star c ⬝ᵥ (N *ᵥ d)) : M = N := by
  rw [ext_iff_mulVec]
  intro d
  funext i
  have := h (Pi.single i 1) d
  simpa [dotProduct, Pi.single_apply] using this
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
