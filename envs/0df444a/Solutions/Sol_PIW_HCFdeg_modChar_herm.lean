-- Prove2me | solution 1 for PIW.HCFdeg.modChar_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:34:07.722845+00:00
-- url     : https://prove2.me/submissions/976fc015-8508-42c9-bd2f-73b05bf6587b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
import Theorems.Thm_PIW_HCFdeg_ext_toM
import Theorems.Thm_PIW_HCFdeg_toM_inv
import Theorems.Thm_PIW_HCFdeg_inUJ_J

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
variable {n : ℕ} (ε : Fin n → Bool)
namespace PIW.HCFdeg
theorem _root_.solution (h : UJ ε) (hh : (toM h)ᴴ = toM h) : Measure.modularCharacter h = 1 := by
  set j := mkU ε (Jm ε) (inUJ_J ε) with hj
  have hjj : j * j = 1 := ext_toM ε (by
    show Jm ε * Jm ε = 1
    exact Jm_mul_self ε)
  have hinv : h⁻¹ = j * h * j := ext_toM ε (by
    rw [toM_inv, hh]
    rfl)
  set D : UJ ε →* ℝ≥0 := Measure.modularCharacter with hD
  have e1 : D j * D j = 1 := by rw [← map_mul, hjj, map_one]
  have e0 : D h * D h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [hinv, map_mul, map_mul] at e0
  have e2 : D h * D h = 1 := by
    rw [← e0, show D h * (D j * D h * D j) = D h * D h * (D j * D j) by ring, e1, mul_one]
  have e3 : ((D h : ℝ)) * (D h : ℝ) = 1 := by exact_mod_cast e2
  rcases mul_self_eq_one_iff.mp e3 with e4 | e4
  · exact_mod_cast e4
  · have := (D h).2
    linarith
end PIW.HCFdeg
