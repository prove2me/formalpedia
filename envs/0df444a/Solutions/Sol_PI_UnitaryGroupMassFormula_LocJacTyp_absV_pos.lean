-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:17.284805+00:00
-- url     : https://prove2.me/submissions/9950ce61-bae6-44d9-9ba9-7c8ab6d4cd1c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_q_pos

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
theorem _root_.solution {x : Fv F v} (hx : x ≠ 0) : 0 < absV v x := by
  have h : Valued.v x ≠ 0 := by simpa using hx
  unfold absV
  rw [dif_neg h]
  exact zpow_pos (q_pos v) _
end PI.UnitaryGroupMassFormula.LocJacTyp
