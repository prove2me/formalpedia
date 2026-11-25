-- Prove2me | solution 1 for PI.BeDiagZp.SubstW.coeff_expTr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:17.351555+00:00
-- url     : https://prove2.me/submissions/99b3a0a3-1053-4b5a-a82c-3f61951c48e7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear

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
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.SubstW
theorem _root_.solution {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (N : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (expTr F N) =
      ∑ n ∈ Finset.range N, MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := by
  simp only [expTr, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]
end PI.BeDiagZp.SubstW
