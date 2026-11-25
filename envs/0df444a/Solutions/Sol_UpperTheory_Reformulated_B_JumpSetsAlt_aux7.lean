-- Prove2me | solution 1 for UpperTheory.Reformulated.B.JumpSetsAlt.aux7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:08.011125+00:00
-- url     : https://prove2.me/submissions/fca6c62b-e40c-4ae4-9a04-6c8f14650b46

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
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L], IsScalarTower ℚ ℚ L := by
  intro L _ _
  infer_instance
end UpperTheory.Reformulated.B.JumpSetsAlt
