-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_linearIndependent_real_of_int_75b3dfee45d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:32.473978+00:00
-- url     : https://prove2.me/submissions/ac27a358-abb6-4cbc-a2e6-5facc32009cb

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
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution {n : ℕ} {b : Fin n → W} (hb : LinearIndependent ℤ b)
    (hd : DiscreteTopology (span ℤ (Set.range b))) : LinearIndependent ℝ b := by
  have h1 := Real.finrank_eq_int_finrank_of_discrete hd
  rw [linearIndependent_iff_card_eq_finrank_span]
  rw [h1, Set.finrank, finrank_span_eq_card hb]
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
