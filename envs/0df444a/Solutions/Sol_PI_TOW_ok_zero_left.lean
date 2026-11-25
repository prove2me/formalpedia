-- Prove2me | solution 1 for PI.TOW.ok_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:11.447837+00:00
-- url     : https://prove2.me/submissions/59f55015-cce1-415d-a7f2-29bec12b1b86

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_OkSmulRight
import Theorems.Thm_PI_TOW_combo_zero
import Theorems.Thm_PI_TOW_fockR_zero_left
import Theorems.Thm_PI_TOW_fockR_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
variable {K : Type} [Field K] {n' m : ℕ} {vec : Fin n' → Bool} {TT : Finset (Fin n')} {d : Fin n' → ℕ} {c : ℕ}
namespace PI.TOW
theorem _root_.solution (s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) :
    Ok K n' m vec TT d c 0 s := by
  refine ⟨0, by simp, fun G _ H _ => ?_⟩
  rw [mul_zero, fockR_zero_right, combo_zero, map_zero, fockR_zero_left]
end PI.TOW
