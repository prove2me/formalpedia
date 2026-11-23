-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_SelectionLemmas_aux2__390a7bbeff16
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:36.610781+00:00
-- url     : https://prove2.me/submissions/789e6226-4137-429a-be45-021362035ae2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.SelectionLemmas
theorem _root_.solution.{u_1} :
    ∀ {K : Type u_1} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))) := by
  intros; infer_instance
end UpperTheory.Reformulated.B.SelectionLemmas
