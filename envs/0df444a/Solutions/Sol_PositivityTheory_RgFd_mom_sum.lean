-- Prove2me | solution 1 for PositivityTheory.RgFd.mom_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:35.897+00:00
-- url     : https://prove2.me/submissions/7fdd57f5-1585-4f63-a17b-d57894774b2c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomentRecursion_MomStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open PositivityTheory PositivityTheory.RgFd
namespace PositivityTheory.RgFd
theorem _root_.solution {A : Type} [MeasurableSpace A] (m : Measure A) {W : A → ℝ} (hW : Measurable W) (h : ∀ x, 0 ≤ W x ∧ W x ≤ 1) :
    m {x | 0 < W x} = ∑' M : ℕ, ∫⁻ x, ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M) ∂m := by
  rw [← lintegral_tsum fun M => (by fun_prop : Measurable fun x => ENNReal.ofReal (W x ^ 1 * (1 - W x) ^ M)).aemeasurable,
    ← lintegral_indicator_one (measurableSet_lt measurable_const hW)]
  refine lintegral_congr fun x => ?_
  have a := (h x).1
  have b := sub_nonneg.2 (h x).2
  by_cases hx : 0 < W x
  · have hs : HasSum (fun M : ℕ => W x ^ 1 * (1 - W x) ^ M) (W x ^ 1 * (1 - (1 - W x))⁻¹) :=
      (hasSum_geometric_of_lt_one b (by linarith)).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun M => by positivity) hs.summable, hs.tsum_eq,
      indicator_of_mem (show x ∈ {x | 0 < W x} from hx)]
    simp [mul_inv_cancel₀ hx.ne']
  · rw [indicator_of_notMem (show x ∉ {x | 0 < W x} from hx), show W x = 0 from le_antisymm (not_lt.1 hx) a]
    simp
end PositivityTheory.RgFd
