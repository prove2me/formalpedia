-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_JumpSetsAlt_sign_action_map_comm__d7dbb2638972
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:31.160382+00:00
-- url     : https://prove2.me/submissions/efaca9d6-7761-4f38-bd89-65737eef78d8

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
theorem _root_.solution.{u_1} :
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), b ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b := by
  intro L _ _ ζ a b
  exact (le_sup_left : UpperTheory.Reformulated.B.JumpSetsAlt.E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))
end UpperTheory.Reformulated.B.JumpSetsAlt
