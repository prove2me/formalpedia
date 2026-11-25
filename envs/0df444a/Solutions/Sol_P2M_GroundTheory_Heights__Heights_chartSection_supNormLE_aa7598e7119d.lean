-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chartSection_supNormLE_aa7598e7119d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:40.799708+00:00
-- url     : https://prove2.me/submissions/2588effb-e1ca-46ef-8366-d47b93dabf93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (P : ArithVariety n) (c0 : (k : ι) → Fin (n k + 1)) :
    (IntegralSection.chartSection P c0).SupNormLE (HermLine.standard n) 0 := by
  intro z hz c d e he hc
  have hpos : 0 < ∏ k, l2Norm (z k) := Finset.prod_pos fun k _ ↦ vectorL2Norm_pos (hz.1 k)
  have h0 : evalCone z (1 * e - chartMonomial c0 1 * chartMonomial c d) = 0 := hz.2 _ he.2
  simp only [evalCone, eval₂_sub, eval₂_mul, one_mul, sub_eq_zero] at h0
  have hm : evalCone z (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  have hmn : 0 < ‖evalCone z (chartMonomial c d)‖ := norm_pos_iff.mpr hm
  change ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * ∏ k, l2Norm (z k)) ≤ Real.exp 0
  have h1 : evalCone z e = evalCone z (chartMonomial c0 1) * evalCone z (chartMonomial c d) := by
    simp only [evalCone]; exact h0
  rw [h1, norm_mul, Real.exp_zero, div_le_one (mul_pos hmn hpos), mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hmn.le
  rw [evalCone_chartMonomial, norm_prod]
  refine Finset.prod_le_prod (fun k _ ↦ norm_nonneg _) (fun k _ ↦ ?_)
  simpa using norm_le_l2Norm (z k) (c0 k)
end GroundTheory.Heights₂.Heights
