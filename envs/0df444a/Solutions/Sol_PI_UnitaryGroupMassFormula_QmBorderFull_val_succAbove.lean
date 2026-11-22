-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.val_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:49.581615+00:00
-- url     : https://prove2.me/submissions/990d4b27-310e-4912-9141-88f727aa3074

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution {t : ℕ} (p : Fin (t + 1)) (i : Fin t) :
    ((p.succAbove i : Fin (t + 1)) : ℕ) = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [if_pos h]
    first
    | exact congrArg Fin.val (Fin.succAbove_of_castSucc_lt p i h)
    | (rw [Fin.succAbove_of_castSucc_lt p i (by simpa [Fin.lt_iff_val_lt_val] using h)]; simp)
  · rw [if_neg h]
    first
    | exact congrArg Fin.val (Fin.succAbove_of_le_castSucc p i (Nat.not_lt.mp h))
    | (rw [Fin.succAbove_of_le_castSucc p i (by simp [Fin.le_iff_val_le_val]; omega)]; simp)
end PI.UnitaryGroupMassFormula.QmBorderFull
