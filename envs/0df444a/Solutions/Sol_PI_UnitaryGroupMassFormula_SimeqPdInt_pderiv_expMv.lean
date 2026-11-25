-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SimeqPdInt.pderiv_expMv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:13.112531+00:00
-- url     : https://prove2.me/submissions/62332e5d-99c6-447e-b4fd-39b2aba5d81f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs
import Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_coeff_expMv_eq_ts
import Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_pderiv_ts

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
theorem _root_.solution (k : σ) {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) :
    pderiv ℂ_[p] k (PI.FglGram.expMv f) = PI.FglGram.expMv f * pderiv ℂ_[p] k f := by
  classical
  ext α
  have hdeg : (α + Finsupp.single k 1).degree ≤ α.degree + 1 := by
    rw [map_add]
    simp
  rw [coeff_pderiv, coeff_expMv_eq_ts hf hdeg, ← coeff_pderiv, pderiv_ts, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = α := by simpa using hq
  have hle : q.1.degree ≤ α.degree := by
    rw [← hq', map_add]
    omega
  rw [coeff_expMv_eq_ts hf hle]
end PI.UnitaryGroupMassFormula.SimeqPdInt
