-- Prove2me | solution 1 for PI.GTNum.mem_R_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:07:14.273317+00:00
-- url     : https://prove2.me/submissions/a20e6afe-2d8a-4001-946c-8d37d3227395

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_CardEraseIccMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_InterlacingDefectEqCard
import Theorems.Thm_PI_GTNum_lam_le_last
import Theorems.Thm_PI_GTNum_sg_le_first
import Theorems.Thm_PI_GTNum_interlacing_defect_le_gap

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
theorem _root_.solution (hI : Interlace h lam sg) (hn : 0 < n) (i : Fin n) (v : ℤ)
    (hv : v ∈ Rset h lam sg i) :
    lam.w ⟨N - 1, by omega⟩ ≤ v ∧
      v ≤ sg.w ⟨0, hn⟩ + (sg.w ⟨0, hn⟩ - lam.w ⟨N - 1, by omega⟩) := by
  unfold Rset at hv
  rw [Finset.mem_Icc] at hv
  have h1 := lam_le_last h lam (i.1 + 1) (by omega)
  have h2 := (hI i).2
  have h3 := sg_le_first sg hn i
  have h4 := interlacing_defect_le_gap h lam sg hI hn
  have h5 := min_le_right (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg)
  constructor <;> omega
end PI.GTNum
