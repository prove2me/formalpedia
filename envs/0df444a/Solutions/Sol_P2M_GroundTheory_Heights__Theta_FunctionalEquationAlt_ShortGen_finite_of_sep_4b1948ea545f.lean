-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_finite_of_sep_4b1948ea545f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:24.311037+00:00
-- url     : https://prove2.me/submissions/9a38cd0a-3cf6-47a4-93a0-c14619ad9def

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_discreteTopology_of_sep_58012c0f5a21
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_lattice_closedBall_e6af14f7c688


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
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution {L : Submodule ℤ W} {lam : ℝ} (hlam : 0 < lam) (h : Sep L lam) (r : ℝ) :
    {x : W | x ∈ L ∧ ‖x‖ ≤ r}.Finite := by
  have := discreteTopology_of_sep hlam h
  exact GroundTheory.Heights₂.Heights.finite_lattice_closedBall L r
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
