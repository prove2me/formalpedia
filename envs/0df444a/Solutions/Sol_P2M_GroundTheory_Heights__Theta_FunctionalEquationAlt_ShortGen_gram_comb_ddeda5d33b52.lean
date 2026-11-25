-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_gram_comb_ddeda5d33b52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:20.976974+00:00
-- url     : https://prove2.me/submissions/be9e5d3c-c6ac-4497-954a-143378e81f7c

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
omit [FiniteDimensional ℝ W]
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution {k l : Type*} [Fintype k] [Fintype l] (A : Matrix k l ℝ) (b : l → W) :
    gram ℝ (fun i => ∑ j, A i j • b j) = A * gram ℝ b * Aᵀ := by
  ext i i'
  simp only [gram, of_apply, mul_apply, transpose_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
