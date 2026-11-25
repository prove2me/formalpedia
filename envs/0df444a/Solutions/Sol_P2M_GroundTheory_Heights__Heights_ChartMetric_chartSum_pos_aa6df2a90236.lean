-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMetric_chartSum_pos_aa6df2a90236
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:23.483398+00:00
-- url     : https://prove2.me/submissions/badf0980-9958-4ee6-bfb1-0010c00fcf8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale
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
open MvPolynomial
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMetric
namespace GroundTheory.Heights₂.Heights.ChartMetric
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {z : Cone n ℂ}
    (hz : BlockNonzero z) (d : ι → ℕ) :
    0 < ∑ c : (k : ι) → Fin (n k + 1), ‖evalCone z (chartMonomial c d)‖ ^ 2 := by
  choose c hc using fun k ↦ Function.ne_iff.mp (hz k)
  have h0 : evalCone z (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h0) 2)
    (Finset.single_le_sum (f := fun c ↦ ‖evalCone z (chartMonomial c d)‖ ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ c))
end GroundTheory.Heights₂.Heights.ChartMetric
