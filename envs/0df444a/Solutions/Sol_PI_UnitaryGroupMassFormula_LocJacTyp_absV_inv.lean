-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.absV_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:21.028919+00:00
-- url     : https://prove2.me/submissions/3faa6960-1c91-44a0-a8f9-a752838e8855

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.LocJacTyp
theorem _root_.solution (x : Fv F v) : absV v x⁻¹ = (absV v x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, absV_zero]
  have h := absV_mul v x x⁻¹
  rw [mul_inv_cancel₀ hx, absV_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm
end PI.UnitaryGroupMassFormula.LocJacTyp
