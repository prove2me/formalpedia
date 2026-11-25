-- Prove2me | solution 1 for PIW.AdelClassFin.DictInter.tau_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:35.694638+00:00
-- url     : https://prove2.me/submissions/919dc9b5-3a45-4ab8-aa88-47b36ff594a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Theorems.Thm_PIW_AdelClassFin_DictInter_tau_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
open PIW.AdelClassFin.DictInter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PIW.AdelClassFin.DictInter
theorem _root_.solution (w e : E) :
    tau w (Formalism.UG.inclE (F := F) (Af F) e) = algebraMap F (Af F) (Algebra.trace F E (w * e)) := by
  show tau w (e ⊗ₜ[F] (1 : Af F)) = _
  rw [tau_tmul, Algebra.algebraMap_eq_smul_one]
end PIW.AdelClassFin.DictInter
