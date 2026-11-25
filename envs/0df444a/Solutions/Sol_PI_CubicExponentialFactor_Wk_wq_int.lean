-- Prove2me | solution 1 for PI.CubicExponentialFactor.Wk.wq_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:22.554611+00:00
-- url     : https://prove2.me/submissions/cf13b995-5e41-4c12-8806-2b61f8ee4c85

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
import Theorems.Thm_PI_CubicExponentialFactor_Wk_norm_add_le_one
import Theorems.Thm_PI_CubicExponentialFactor_Wk_trunc_mul
import Theorems.Thm_PI_CubicExponentialFactor_Wk_term_int
import Theorems.Thm_PI_CubicExponentialFactor_Wk_term_int1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CubicExponentialFactor PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor
variable {p : ℕ} [Fact p.Prime]
namespace PI.CubicExponentialFactor.Wk
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (ha1 : IsIntP W.a₁)
    (ha2 : IsIntP W.a₂) (ha3 : IsIntP W.a₃) (ha4 : IsIntP W.a₄) (ha6 : IsIntP W.a₆)
    (hW : IsWq W wq) : ∀ k, ‖PowerSeries.coeff k wq‖ ≤ 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have h2 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 2)‖ ≤ 1 := by
      rw [pow_two]
      exact trunc_mul ih ih
    have h3 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 3)‖ ≤ 1 := by
      have e : wq ^ 3 = wq ^ 2 * wq := by ring
      rw [e]
      exact trunc_mul h2 ih
    dsimp only [IsWq] at hW
    rw [hW]
    simp only [map_add]
    refine norm_add_le_one (norm_add_le_one (norm_add_le_one (norm_add_le_one
      (norm_add_le_one ?_ ?_) ?_) ?_) ?_) ?_
    · rw [PowerSeries.coeff_one]
      split_ifs <;> simp
    · exact term_int1 ha1 ih
    · exact term_int ha2 (by norm_num) ih
    · exact term_int ha3 (by norm_num) h2
    · exact term_int ha4 (by norm_num) h2
    · exact term_int ha6 (by norm_num) h3
end PI.CubicExponentialFactor.Wk
