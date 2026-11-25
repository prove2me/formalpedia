-- Prove2me | solution 1 for PI.BeDiagZp.expT_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:59.690635+00:00
-- url     : https://prove2.me/submissions/a38306dd-45da-4124-ba59-3ae800fced36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
import Theorems.Thm_PI_BeDiagZp_inv_fact_mul_choose

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
theorem _root_.solution (x y : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    expT (x + y) N = ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range (N - m),
      (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)) := by
  rw [← Finset.sum_range_diag_flip N
    (fun m j => (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)))]
  unfold expT
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [add_pow, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  rw [← inv_fact_mul_choose n m hmn, mul_comm _ (n.choose m : ℂ_[p]), ← smul_smul,
    mul_comm _ ((n.choose m : ℕ) : MvPowerSeries σ ℂ_[p]), ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul]
  exact smul_comm _ _ _
end PI.BeDiagZp
