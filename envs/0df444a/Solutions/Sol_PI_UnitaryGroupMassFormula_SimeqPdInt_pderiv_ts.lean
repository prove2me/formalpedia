-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SimeqPdInt.pderiv_ts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:30.120541+00:00
-- url     : https://prove2.me/submissions/c262d576-e88f-4c65-ab8e-2373ba24b576

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SimeqPdInt
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.UnitaryGroupMassFormula.SimeqPdInt
theorem _root_.solution (k : σ) (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    pderiv ℂ_[p] k (ts f (N + 1)) = ts f N * pderiv ℂ_[p] k f := by
  simp only [ts, map_sum, Finset.sum_mul]
  rw [Finset.sum_range_succ']
  rw [pow_zero, Derivation.map_smul, pderiv_one, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Derivation.map_smul, pderiv_pow, Nat.add_sub_cancel, Algebra.smul_def, Algebra.smul_def]
  have h1 : ((n + 1 : ℕ) : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n.factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hc : (n.factorial : ℂ_[p])⁻¹ =
      ((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p]) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp
  rw [hc, map_mul, map_natCast]
  ring
end PI.UnitaryGroupMassFormula.SimeqPdInt
