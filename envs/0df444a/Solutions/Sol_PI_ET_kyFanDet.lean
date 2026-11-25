-- Prove2me | solution 1 for PI.ET.kyFanDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:07.264964+00:00
-- url     : https://prove2.me/submissions/85fcca3c-6aec-4022-948f-61acc59ee11c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ProdLeOfInjective
import Theorems.Thm_PI_ET_kyFan_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ET
namespace PI.ET
theorem _root_.solution : KyFanDet := by
  intro n k hk p W V hp hpos hW hV
  have hW1 : Wᴴ * W = 1 := by
    have := (mem_unitaryGroup_iff').1 hW
    rwa [star_eq_conjTranspose] at this
  have hW2 : W * Wᴴ = 1 := by
    have := (mem_unitaryGroup_iff).1 hW
    rwa [star_eq_conjTranspose] at this
  have e1 : Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V =
      (Wᴴ * V)ᴴ * diagonal (fun i => (p i : ℂ)) * (Wᴴ * V) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have e2 : (Wᴴ * V)ᴴ * (Wᴴ * V) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc W,
      hW2, Matrix.one_mul, hV]
  rw [e1]
  exact kyFan_diag hk p hp hpos (Wᴴ * V) e2
end PI.ET
