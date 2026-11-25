-- Prove2me | solution 1 for PI.ScRefExists.UnitaryGroupMassFormula.target_of_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:19.602931+00:00
-- url     : https://prove2.me/submissions/9e6f241e-dfee-4a88-ba73-cd8b9f7025fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HypsNonvacuous
import Theorems.Thm_PI_ScRefExists_UnitaryGroupMassFormula_refData_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.UnitaryGroupMassFormula
theorem _root_.solution (h : TargetTwo) : Target := by
  unfold TargetTwo at h
  unfold Target
  intro J g r k e f hg hs hn he hf hef hin
  rcases Nat.lt_or_ge g 2 with hlt | hge
  · obtain rfl : g = 1 := by omega
    exact refData_one J r k e f hin
  · exact h J g r k e f hge hs hn he hf hef hin
end PI.ScRefExists.UnitaryGroupMassFormula
