-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefOp_norm_exp_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:06.798041+00:00
-- url     : https://prove2.me/submissions/d2c9f3e3-ab29-42d3-90a1-1eb995d96713

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    ‖NormedSpace.exp T‖ ≤ Real.exp ‖T‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  dsimp only
  refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) T)).trans ?_
  refine Summable.tsum_le_tsum (fun k => ?_) (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) T)
    (NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖T‖)
  rw [norm_smul, smul_eq_mul, norm_inv, Complex.norm_natCast]
  gcongr
  cases k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k => exact norm_pow_le' T (Nat.succ_pos k)
end ReciprocityTheory.ChartRestriction.DS
