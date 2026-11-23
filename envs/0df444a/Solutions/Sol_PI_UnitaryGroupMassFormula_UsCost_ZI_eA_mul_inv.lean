-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.eA_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:22.594391+00:00
-- url     : https://prove2.me/submissions/9035d49f-d46f-4e43-8838-830d3729e5ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_eA_apply

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
theorem _root_.solution {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    eA s Z * eA s (invF s Z) = 1 ∧ eA s (invF s Z) * eA s Z = 1 := by
  have hu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr h
  have hinv : Matrix.of (invF s Z) = (Matrix.of Z)⁻¹ := by simp [invF]
  constructor <;> ext1 v <;>
    simp only [ContinuousLinearMap.mul_apply, eA_apply, ContinuousLinearMap.one_apply,
      Matrix.mulVec_mulVec, hinv, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec]
end PI.UnitaryGroupMassFormula.UsCost.ZI
