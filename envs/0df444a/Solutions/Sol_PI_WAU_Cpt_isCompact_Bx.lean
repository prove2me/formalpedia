-- Prove2me | solution 1 for PI.WAU.Cpt.isCompact_Bx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:50.342817+00:00
-- url     : https://prove2.me/submissions/847e5866-2a44-42d6-8ee7-c0d57fb89245

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Theorems.Thm_PI_WAU_isCompact_Ohat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)
end PI.WAU.Cpt
