-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DiagRank.exists_int_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:20.216175+00:00
-- url     : https://prove2.me/submissions/99a4574d-63d7-4121-9b23-da663532311c

import Definitions.Def_Formalism_PeriodIntegrals_DiagRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalRank_DetOneSubPNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DiagRank
open Finset
namespace PI.UnitaryGroupMassFormula.DiagRank
theorem _root_.solution {p : ℕ} [Fact p.Prime] (D : ℤ) (x : ℚ_[p]) (hx : x ≠ 0 → D < x.valuation) :
    ∃ u : ℤ_[p], x = (p : ℚ_[p]) ^ (D + 1) * (u : ℚ_[p]) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  have hv := hx h0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℚ_[p]) ^ (D + 1) ≠ 0 := zpow_ne_zero _ hp0
  have hnp : ‖(p : ℚ_[p]) ^ (D + 1)‖ = (p : ℝ) ^ (-(D + 1)) := by
    rw [norm_zpow, Padic.norm_p, inv_zpow', zpow_neg]
  refine ⟨⟨x / (p : ℚ_[p]) ^ (D + 1), ?_⟩, ?_⟩
  · rw [norm_div, hnp, Padic.norm_eq_zpow_neg_valuation h0]
    rw [div_le_one (zpow_pos (by linarith) _)]
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  · show x = (p : ℚ_[p]) ^ (D + 1) * (x / (p : ℚ_[p]) ^ (D + 1))
    field_simp
end PI.UnitaryGroupMassFormula.DiagRank
