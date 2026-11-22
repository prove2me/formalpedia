-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_JumpSetsAlt_algebra_smulCommClass_complex__5a4bc5fe7431
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:20.715798+00:00
-- url     : https://prove2.me/submissions/a8c23f9a-f0f8-4db2-81dd-049db4a50e80

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
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), a ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b := by
  intro L _ _ ζ a b
  exact (le_sup_left : UpperTheory.Reformulated.B.JumpSetsAlt.E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))
end UpperTheory.Reformulated.B.JumpSetsAlt
