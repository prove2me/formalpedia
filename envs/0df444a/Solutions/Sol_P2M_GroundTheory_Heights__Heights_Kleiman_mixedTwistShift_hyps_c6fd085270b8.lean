-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mixedTwistShift_hyps_c6fd085270b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:03:25.65192+00:00
-- url     : https://prove2.me/submissions/419c4de9-3b84-4fd4-b914-f27380e2e701

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (k : Type u) [Field k] :
    (primeOf (S := k) (genericPt k 1)).IsPrime ∧
      (∀ f ∈ primeOf (S := k) (genericPt k 1), ∀ d : ℕ,
        homogeneousComponent d f ∈ primeOf (S := k) (genericPt k 1)) ∧
      primeOf (S := k) (genericPt k 1) ≤ primeOf (S := k) (genericPt k 1) ∧
      ringKrullDim (Poly k 1 ⧸ primeOf (S := k) (genericPt k 1)) ≤ ((1 + 1 : ℕ) : WithBot ℕ∞) ∧
      Nonempty (Fin 1 → LineBundle k (genericPt k 1)) :=
  ⟨(isSubvar_genericPt k 1).isPrime, (isSubvar_genericPt k 1).homog, le_rfl,
    (isSubvar_genericPt k 1).dim.le, ⟨![twistBundle k (genericPt k 1) 1]⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman
