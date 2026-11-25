-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SimeqPdInt.int_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:43:23.734579+00:00
-- url     : https://prove2.me/submissions/d56877b5-5cf3-4398-9174-842bf546409b

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
theorem _root_.solution (k : σ) {F : MvPowerSeries σ ℂ_[p]} (hF : PI.FglGram.IntegralMv F) :
    PI.FglGram.IntegralMv (pderiv ℂ_[p] k F) := by
  intro n
  have hn := hF (n + Finsupp.single k 1)
  unfold PI.FglGram.IsIntP at hn ⊢
  rw [coeff_pderiv, norm_mul]
  refine mul_le_one₀ hn (norm_nonneg _) ?_
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n k + 1)
  push_cast at this
  exact this
end PI.UnitaryGroupMassFormula.SimeqPdInt
