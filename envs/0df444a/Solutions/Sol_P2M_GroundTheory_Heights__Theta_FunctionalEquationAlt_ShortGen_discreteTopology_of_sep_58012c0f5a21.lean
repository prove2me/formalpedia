-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_discreteTopology_of_sep_58012c0f5a21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:16.543852+00:00
-- url     : https://prove2.me/submissions/d605e8c8-6029-4881-8476-1c597ff94a24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
omit [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution {L : Submodule ℤ W} {lam : ℝ} (hlam : 0 < lam) (h : Sep L lam) :
    DiscreteTopology L := by
  refine DiscreteTopology.of_forall_le_dist hlam fun x y hxy => ?_
  show lam ≤ dist x y
  rw [Subtype.dist_eq, dist_eq_norm]
  have hne : (x : W) - y ≠ 0 := sub_ne_zero.2 fun h' => hxy (Subtype.ext h')
  exact h _ (L.sub_mem x.2 y.2) hne
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
