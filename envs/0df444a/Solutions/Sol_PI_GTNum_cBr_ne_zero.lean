-- Prove2me | solution 1 for PI.GTNum.cBr_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:45.141059+00:00
-- url     : https://prove2.me/submissions/5d6c1cf7-8210-4b6d-bcf7-160f5483cfb3

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
theorem _root_.solution (hI : Interlace h lam sg) : cBr h lam sg ≠ 0 := by
  unfold cBr
  refine Finset.prod_ne_zero_iff.2 (fun i _ => Finset.prod_ne_zero_iff.2 (fun v hv =>
    Finset.prod_ne_zero_iff.2 (fun j _ => ?_)))
  have hvs : v ≠ sg.w i := Finset.ne_of_mem_erase hv
  have hvR := Finset.mem_of_mem_erase hv
  unfold Rset at hvR
  rw [Finset.mem_Icc] at hvR
  have h5 := min_le_left (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg)
  rcases lt_trichotomy j.1 i.1 with hji | hji | hji
  · have a1 : lam.w ⟨i.1, by omega⟩ ≤ lam.w ⟨j.1 + 1, by omega⟩ := lam.anti (Fin.mk_le_mk.2 (by omega))
    have a2 := (hI j).2
    omega
  · have e : j = i := Fin.ext hji
    subst e
    omega
  · have a1 : lam.w ⟨j.1, by omega⟩ ≤ lam.w ⟨i.1 + 1, by omega⟩ := lam.anti (Fin.mk_le_mk.2 (by omega))
    have a2 := (hI j).1
    omega
end PI.GTNum
