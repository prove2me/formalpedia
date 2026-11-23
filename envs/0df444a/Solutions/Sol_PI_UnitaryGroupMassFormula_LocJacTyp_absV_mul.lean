-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.absV_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:17.247282+00:00
-- url     : https://prove2.me/submissions/6f07a877-1a24-4a7b-a5f9-6a9c900b99a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_q_pos
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_zero

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
theorem _root_.solution (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  by_cases hx : x = 0
  · simp [hx, absV_zero]
  by_cases hy : y = 0
  · simp [hy, absV_zero]
  have h1 : Valued.v x ≠ 0 := by simpa using hx
  have h2 : Valued.v y ≠ 0 := by simpa using hy
  have h3 : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  unfold absV
  rw [dif_neg h1, dif_neg h2, dif_neg h3, ← zpow_add₀ (q_pos v).ne', ← toAdd_mul]
  congr 2
  apply WithZero.coe_injective
  rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
end PI.UnitaryGroupMassFormula.LocJacTyp
