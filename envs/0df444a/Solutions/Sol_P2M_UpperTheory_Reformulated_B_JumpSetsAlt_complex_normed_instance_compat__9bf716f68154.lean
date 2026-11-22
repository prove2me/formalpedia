-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_JumpSetsAlt_complex_normed_instance_compat__9bf716f68154
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:23.895486+00:00
-- url     : https://prove2.me/submissions/5085d05e-5861-45fd-b85e-c056e285e150

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
    ∀ {L : Type u_1} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), ζ + ζ⁻¹ ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b := by
  intro L _ _ ζ a b
  exact (le_sup_right : UpperTheory.Reformulated.B.JumpSetsAlt.F1 ζ ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))
end UpperTheory.Reformulated.B.JumpSetsAlt
