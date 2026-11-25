-- Prove2me | solution 1 for PI.GTNum.mem_R_bounds_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:59.805958+00:00
-- url     : https://prove2.me/submissions/bfb62d50-3f72-44ae-aef1-5c346b80d390

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_NumMore
import Theorems.Thm_PI_GTNum_lam_le_last


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
theorem _root_.solution (i : Fin n) (v : ℤ) (hv : v ∈ Rset h lam sg i) :
    lam.w ⟨N - 1, by omega⟩ ≤ v ∧ v ≤ lam.w ⟨0, by omega⟩ := by
  unfold Rset at hv
  rw [Finset.mem_Icc] at hv
  have h1 := lam_le_last h lam (i.1 + 1) (by omega)
  have h2 : lam.w ⟨i.1, by omega⟩ ≤ lam.w ⟨0, by omega⟩ := lam.anti (Fin.mk_le_mk.2 (Nat.zero_le _))
  have h5 := min_le_left (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg)
  constructor <;> omega
end PI.GTNum
