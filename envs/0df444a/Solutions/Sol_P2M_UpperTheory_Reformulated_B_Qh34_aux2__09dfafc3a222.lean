-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qh34_aux2__09dfafc3a222
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:19:38.385116+00:00
-- url     : https://prove2.me/submissions/1bba8587-ad67-4922-9abe-c6dff5e548dc

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

namespace UpperTheory.Reformulated.B.Qh34.aux2
theorem _root_.solution.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x y : NumberField.InfiniteAdeleRing K),
      ∑ w : NumberField.InfinitePlace K,
          (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) ((x + y) w)).re =
        ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re +
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (y w)).re := by
  intro K _ _ x y
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (x + y) w = x w + y w := rfl
  rw [h, map_add, Complex.add_re, mul_add]
end UpperTheory.Reformulated.B.Qh34.aux2
