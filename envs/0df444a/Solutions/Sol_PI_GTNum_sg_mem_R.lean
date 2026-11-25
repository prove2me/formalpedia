-- Prove2me | solution 1 for PI.GTNum.sg_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:02.909523+00:00
-- url     : https://prove2.me/submissions/704fb644-4d07-40a9-beca-09c74f70f86a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Theorems.Thm_PI_GTNum_term_le_D0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GTNum
open Formalism.BasicNotions PI Finset
variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
namespace PI.GTNum
theorem _root_.solution (hI : Interlace h lam sg) (i : Fin n) : sg.w i ∈ Rset h lam sg i := by
  unfold Rset
  have h1 := hI i
  have h2 := term_le_D0 h lam sg hI i
  rw [Finset.mem_Icc]
  refine ⟨h1.2, le_min h1.1 (by omega)⟩
end PI.GTNum
