-- Prove2me | solution 1 for PI.BeDiagZp.inv_fact_mul_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:58.465457+00:00
-- url     : https://prove2.me/submissions/01c9efc8-1982-4df1-aa8b-6f0694ce08d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp
open MvPowerSeries
open IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.BeDiagZp
theorem _root_.solution (n m : ℕ) (h : m ≤ n) :
    (n.factorial : ℂ_[p])⁻¹ * (n.choose m : ℂ_[p]) =
      (m.factorial : ℂ_[p])⁻¹ * ((n - m).factorial : ℂ_[p])⁻¹ := by
  have h1 := Nat.choose_mul_factorial_mul_factorial h
  have hn : (n.factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hm : (m.factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hk : ((n - m).factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (n.choose m : ℂ_[p]) * m.factorial * (n - m).factorial = n.factorial := by
    exact_mod_cast h1
  field_simp
  exact h2
end PI.BeDiagZp
