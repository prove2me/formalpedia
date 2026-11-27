-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.absV_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:17:49.084013+00:00
-- url     : https://prove2.me/submissions/adbb36fc-f799-46ca-9763-ef8d8608d44b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_inv

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
theorem _root_.solution (x y : Fv F v) : absV v (x / y) = absV v x / absV v y := by
  rw [div_eq_mul_inv, absV_mul, absV_inv, div_eq_mul_inv]
end PI.UnitaryGroupMassFormula.LocJacTyp
