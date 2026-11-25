-- Prove2me | solution 1 for PI.GTNum.term_le_D0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:07.156777+00:00
-- url     : https://prove2.me/submissions/96a27662-466e-4bf7-9257-8d1a413dc9f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Theorems.Thm_PI_GTNum_term_nonneg

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
theorem _root_.solution (hI : Interlace h lam sg) (i : Fin n) :
    sg.w i - lam.w ⟨i.1 + 1, by omega⟩ ≤ D0 h lam sg :=
  Finset.single_le_sum (f := fun i : Fin n => sg.w i - lam.w ⟨i.1 + 1, by omega⟩)
    (fun j _ => term_nonneg h lam sg hI j) (Finset.mem_univ i)
end PI.GTNum
