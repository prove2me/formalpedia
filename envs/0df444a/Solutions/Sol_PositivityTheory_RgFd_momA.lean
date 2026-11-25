-- Prove2me | solution 1 for PositivityTheory.RgFd.momA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:53.509928+00:00
-- url     : https://prove2.me/submissions/28860b27-90e4-4ca8-b377-a58bb95ac179

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomentRecursion_MomStep
import Theorems.Thm_PositivityTheory_RgFd_mom_step
import Theorems.Thm_PositivityTheory_RgFd_mom_sum

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
theorem _root_.solution : MomA := by
  intro Ω Ω' _ _ ν ν' U U' t0 hU hU' h h' ht he hf
  have p : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → {x | 0 < W x} = {x | 0 < W x ^ t0} := fun W h => by
    ext x
    show 0 < W x ↔ 0 < W x ^ t0
    exact ⟨fun a => pow_pos a _, fun a => (h x).1.lt_of_ne fun b => by
      rw [← b, zero_pow (by omega)] at a; exact lt_irrefl _ a⟩
  have q : ∀ {A : Type} (W : A → ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) → ∀ x, 0 ≤ W x ^ t0 ∧ W x ^ t0 ≤ 1 := fun W h x =>
    ⟨pow_nonneg (h x).1 _, pow_le_one₀ (h x).1 (h x).2⟩
  rw [p U h, p U' h', mom_sum ν (hU.pow_const t0) (q U h), mom_sum ν' (hU'.pow_const t0) (q U' h')]
  refine tsum_congr fun M => mom_step (hU.pow_const t0) (hU'.pow_const t0) (q U h) (q U' h') (fun j hj => ?_)
    (fun j hj => ?_) M 1 le_rfl
  · simpa only [← pow_mul, mul_comm t0] using he j hj
  · simpa only [← pow_mul, mul_comm t0] using hf j hj
end PositivityTheory.RgFd
