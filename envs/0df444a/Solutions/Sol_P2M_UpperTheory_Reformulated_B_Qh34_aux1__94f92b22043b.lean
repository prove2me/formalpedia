-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qh34_aux1__94f92b22043b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:28.899602+00:00
-- url     : https://prove2.me/submissions/efe44c65-ed5a-4ea9-a87c-8a7f506a73ab

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteTraceAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh34.aux1
theorem _root_.solution.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],
      ∑ x : NumberField.InfinitePlace K,
          (↑x.mult : ℝ) *
            ((NumberField.InfinitePlace.Completion.extensionEmbedding x : x.Completion → ℂ)
                ((0 : NumberField.InfiniteAdeleRing K) x)).re =
        (0 : ℝ) := by
  intro K _ _
  refine Finset.sum_eq_zero fun w _ => ?_
  have h : (0 : NumberField.InfiniteAdeleRing K) w = 0 := rfl
  rw [h, map_zero, Complex.zero_re, mul_zero]
end UpperTheory.Reformulated.B.Qh34.aux1
