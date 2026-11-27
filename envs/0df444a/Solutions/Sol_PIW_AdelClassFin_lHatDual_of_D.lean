-- Prove2me | solution 1 for PIW.AdelClassFin.lHatDual_of_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:44.441121+00:00
-- url     : https://prove2.me/submissions/cd73b3ac-bfc2-4e05-a4d1-063af83d815e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
import Theorems.Thm_PIW_AdelClassFin_dual_hat_integral
import Theorems.Thm_PIW_AdelClassFin_lDenom_of
import Theorems.Thm_PIW_AdelClassFin_lDense_of
import Theorems.Thm_PIW_AdelClassFin_lHatDual_of

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
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (h₁ : DInter) (h₂ : DDenom) (h₃ : DDense) : LHatDual := by
  exact lHatDual_of h₁ (lDenom_of h₂) (lDense_of h₃) dual_hat_integral
end PIW.AdelClassFin
