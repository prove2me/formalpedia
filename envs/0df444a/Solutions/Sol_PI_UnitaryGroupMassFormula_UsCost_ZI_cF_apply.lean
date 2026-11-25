-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.cF_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:52:33.901486+00:00
-- url     : https://prove2.me/submissions/169323a8-5402-4828-9520-0c939f1ee1f2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_eA_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_inverse_eA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution (i : Fin s × Fin s × Bool) {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0)
    (W : Fin s → Fin s → ℂ) :
    cF s i Z W = if i.2.2 then (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).re
      else (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).im := by
  have hinv : Matrix.of (invF s Z) = (Matrix.of Z)⁻¹ := by simp [invF]
  rw [cF, inverse_eA s h]
  show lamL s i.1 i.2.1 i.2.2 (eA s (invF s Z)) W = _
  rw [lamL_apply, eA_apply, hinv]
  have e : ((Matrix.of Z)⁻¹.mulVec fun c => W c i.2.1) i.1
      = ((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1 := by
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
  rw [e]
end PI.UnitaryGroupMassFormula.UsCost.ZI
