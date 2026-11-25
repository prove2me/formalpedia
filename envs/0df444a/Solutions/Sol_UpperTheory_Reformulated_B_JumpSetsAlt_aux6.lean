-- Prove2me | solution 1 for UpperTheory.Reformulated.B.JumpSetsAlt.aux6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:01:40.85681+00:00
-- url     : https://prove2.me/submissions/4fbbf308-fae2-4c6f-b9b2-6f57a98e79ce

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_JumpSets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open scoped Classical
namespace UpperTheory.Reformulated.B.JumpSetsAlt
theorem _root_.solution :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L), CharZero ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) := by
  intro L _ _ ζ a b
  infer_instance
end UpperTheory.Reformulated.B.JumpSetsAlt
