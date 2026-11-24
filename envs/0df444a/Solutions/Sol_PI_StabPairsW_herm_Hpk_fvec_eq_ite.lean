-- Prove2me | solution 1 for PI.StabPairsW.herm_Hpk_fvec_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:48.412702+00:00
-- url     : https://prove2.me/submissions/4584720b-a79e-4fdb-bb91-bf8b21c4a787

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_herm_swap
import Theorems.Thm_PI_StabPairsW_herm_e
import Theorems.Thm_PI_StabPairsW_z_esI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z c) z = if c = Fin.last r then herm (Hpk k r) z z else 0 := by
  by_cases hc : c.val < r
  · have hne : c ≠ Fin.last r := fun h => by rw [h] at hc; simp at hc
    rw [if_neg hne]
    simp only [fvec, dif_pos hc]
    rw [herm_swap, herm_e, z_esI z hz]
    simp
  · have heq : c = Fin.last r := Fin.ext (by have := c.isLt; simp; omega)
    rw [if_pos heq]
    simp only [fvec, dif_neg hc]
end PI.StabPairsW
