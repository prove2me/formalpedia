-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_norm_pos_9178f4bb2177
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:42.834155+00:00
-- url     : https://prove2.me/submissions/f0c0a345-f986-4723-af98-b5e9a5159b45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
open Matrix
namespace GroundTheory.Heights₂.Heights
namespace HermNorm
theorem _root_.solution (h : HermNorm n) {v : Fin n → ℂ} (hv : v ≠ 0) : 0 < h.norm v := by
  unfold HermNorm.norm
  apply Real.sqrt_pos.mpr
  have hAv : h.mat *ᵥ v ≠ 0 := by
    intro h0
    apply hv
    have := congrArg (fun x => h.mat⁻¹ *ᵥ x) h0
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hAv
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩
end HermNorm
end GroundTheory.Heights₂.Heights
