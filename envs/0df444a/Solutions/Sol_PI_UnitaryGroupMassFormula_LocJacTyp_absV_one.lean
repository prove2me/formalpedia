-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.absV_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:11.108487+00:00
-- url     : https://prove2.me/submissions/7b3e85e0-d5f5-47b6-9475-dc258e2dff31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs

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
theorem _root_.solution : absV v (1 : Fv F v) = 1 := by
  have h : Valued.v (1 : Fv F v) ≠ 0 := by simp
  unfold absV
  rw [dif_neg h]
  have h1 : WithZero.unzero h = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [h1, toAdd_one, zpow_zero]
end PI.UnitaryGroupMassFormula.LocJacTyp
