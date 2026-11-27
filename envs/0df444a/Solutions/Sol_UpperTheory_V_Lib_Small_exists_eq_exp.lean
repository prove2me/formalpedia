-- Prove2me | solution 1 for UpperTheory.V.Lib.Small.exists_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:40.119186+00:00
-- url     : https://prove2.me/submissions/dc3e1c8c-c5ac-475b-91c7-ec938e80f6d9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IntegralityNearIdentity_EqOneOfNear
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjugateOfRoots
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WeightedSumBis
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IntegralityNearIdentity_ExistsContDiffEventuallyEq
import Theorems.Thm_UpperTheory_Reformulated_B_weightedSumBis_exists_eq_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open UpperTheory UpperTheory.V UpperTheory.V.Lib UpperTheory.V.Lib.Small
namespace UpperTheory.V.Lib.Small
theorem _root_.solution (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 = 1) (hm : ∀ x y, f (x + y) = f x * f y) :
    ∃ c : ℂ, ∀ x : ℝ, f x = Complex.exp (c * x) :=
  _root_.UpperTheory.Reformulated.B.weightedSumBis.exists_eq_exp f hc h0 hm
end UpperTheory.V.Lib.Small
