-- Prove2me | solution 1 for PI.Residue.tsum_pi_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:53.41922+00:00
-- url     : https://prove2.me/submissions/ac8cac62-c76b-4d9d-99d7-e7461e476d03

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open scoped ENNReal
namespace PI.Residue
theorem _root_.solution (w : ℕ → ℝ≥0∞) (m : ℕ) :
    ∑' v : Fin m → ℕ, ∏ i, w (v i) = (∑' n, w n) ^ m := by
  induction m with
  | zero => simp [tsum_fintype]
  | succ m ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)).tsum_eq, ENNReal.tsum_prod']
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]
    rw [pow_succ, mul_comm]
end PI.Residue
