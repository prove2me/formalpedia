-- Prove2me | solution 1 for PI.SSE.reduceBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:32.32648+00:00
-- url     : https://prove2.me/submissions/9fb216ee-eb06-4d4c-b6b9-f0ea5ed495f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Reduce
import Theorems.Thm_PI_SSE_lattice_span_comm
import Theorems.Thm_PI_SSE_reduce_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups Modular
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution : ReduceBasis := by
  intro w₁ w₂ hw
  rcases lt_or_gt_of_ne hw with h | h
  · have h' : 0 < ((starRingEnd ℂ) w₂ * w₁).im := by
      have e : ((starRingEnd ℂ) w₂ * w₁).im = -((starRingEnd ℂ) w₁ * w₂).im := by
        simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
        ring
      linarith
    obtain ⟨v₁, v₂, h1, h2, h3, h4⟩ := reduce_pos w₂ w₁ h'
    exact ⟨v₁, v₂, h1, by rw [h2, lattice_span_comm], h3, h4⟩
  · exact reduce_pos w₁ w₂ h
end PI.SSE
