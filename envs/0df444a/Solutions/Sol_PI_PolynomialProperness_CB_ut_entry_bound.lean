-- Prove2me | solution 1 for PI.PolynomialProperness.CB.ut_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:19.487628+00:00
-- url     : https://prove2.me/submissions/f67fd64b-3e78-4fe7-b8ed-432e0e886a56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
import Theorems.Thm_PI_PolynomialProperness_CB_det_norm_le
import Theorems.Thm_PI_PolynomialProperness_CB_ut_entry_eq_det
import Theorems.Thm_PI_PolynomialProperness_GN_entry_le_mx
import Theorems.Thm_PI_PolynomialProperness_GN_mx_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB
namespace PI.PolynomialProperness.CB
theorem _root_.solution {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : ‖U i j‖ ≤ m.factorial * (1 + mx (L * U)) ^ m := by
  rw [ut_entry_eq_det hL hU i j]
  have hd := det_norm_le ((L * U).submatrix (rws i) (cls i j)) (c := mx (L * U))
    (fun a b => GN.entry_le_mx (L * U) (rws i a) (cls i j b))
  rw [Fintype.card_fin] at hd
  have hx := GN.mx_nonneg (L * U)
  have hi : i.val + 1 ≤ m := Nat.succ_le_of_lt i.isLt
  have h1 : ((i.val + 1).factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hi
  have h2 : mx (L * U) ^ (i.val + 1) ≤ (1 + mx (L * U)) ^ m :=
    (pow_le_pow_left₀ hx (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hi)
  exact hd.trans (mul_le_mul h1 h2 (pow_nonneg hx _) (by positivity))
end PI.PolynomialProperness.CB
