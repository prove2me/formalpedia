-- Prove2me | solution 1 for PI.PolynomialProperness.CB.inv_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:26.796335+00:00
-- url     : https://prove2.me/submissions/283b7364-02f2-4c5e-9eeb-a1e409ff6dcb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
import Theorems.Thm_PI_PolynomialProperness_CB_det_norm_le

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
theorem _root_.solution {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hM : M.det = 1) {c : ℝ}
    (hc : ∀ i j, ‖M i j‖ ≤ c) (i j : Fin (n + 1)) : ‖M⁻¹ i j‖ ≤ n.factorial * c ^ n := by
  rw [inv_def, hM, Ring.inverse_one, one_smul, adjugate_fin_succ_eq_det_submatrix, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have := det_norm_le (M.submatrix j.succAbove i.succAbove) (fun a b => hc _ _)
  rwa [Fintype.card_fin] at this
end PI.PolynomialProperness.CB
