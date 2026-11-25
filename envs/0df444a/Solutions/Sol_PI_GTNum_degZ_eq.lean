-- Prove2me | solution 1 for PI.GTNum.degZ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:51.041135+00:00
-- url     : https://prove2.me/submissions/1be73015-cff8-4085-926b-2b06a5a0ffee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_NumMore

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
theorem _root_.solution : degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg := by
  subst h
  unfold degZ wsum D0
  rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]
  have e1 : ∑ i : Fin n, lam.w i.succ = ∑ i : Fin n, lam.w ⟨i.1 + 1, by omega⟩ := rfl
  have e0 : lam.w 0 = lam.w ⟨0, by omega⟩ := rfl
  rw [e1, e0]
  ring
end PI.GTNum
