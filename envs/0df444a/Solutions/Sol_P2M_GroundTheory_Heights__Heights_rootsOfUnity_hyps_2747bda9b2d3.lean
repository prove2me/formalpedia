-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_rootsOfUnity_hyps_2747bda9b2d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:12:59.814554+00:00
-- url     : https://prove2.me/submissions/648aa57c-1703-44c0-82b8-c0df4287d21a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    Nat.Prime 2 ∧ IsPrimitiveRoot (-1 : 𝓞 ℚ) 2 ∧ (1 : 𝓞 ℚ) ^ 2 = 1 ∧ (-1 : 𝓞 ℚ) ^ 2 = 1 ∧
      (1 : 𝓞 ℚ) ≠ -1 := by
  have hne : (1 : 𝓞 ℚ) ≠ -1 := by
    intro h
    have := congrArg (fun x : 𝓞 ℚ ↦ (x : ℚ)) h
    norm_num at this
  refine ⟨Nat.prime_two, ?_, by simp, by simp, hne⟩
  refine IsPrimitiveRoot.mk_of_lt (-1) (by norm_num) (by simp) fun l hl0 hl2 hl ↦ ?_
  interval_cases l
  exact absurd (by simpa using hl) (Ne.symm hne)
end GroundTheory.Heights₂.Heights
