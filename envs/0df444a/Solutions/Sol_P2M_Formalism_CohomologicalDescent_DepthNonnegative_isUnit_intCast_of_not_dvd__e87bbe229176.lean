-- Prove2me | solution 1 for P2M_Formalism_CohomologicalDescent_DepthNonnegative_isUnit_intCast_of_not_dvd__e87bbe229176
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:38.074134+00:00
-- url     : https://prove2.me/submissions/78c91e97-3eaa-4d49-a22d-38f7a57ccab7

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution (R : Type) [CommRing R] (l : ℕ) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R))
    (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : IsUnit (m : R) := by
  have h1 : ¬ l ∣ m.natAbs := fun h => hm (Int.natCast_dvd.mpr h)
  have h2 := hu _ h1
  rcases Int.natAbs_eq m with h | h
  · have e : (m : R) = ((m.natAbs : ℕ) : R) := by
      conv_lhs => rw [h]
      simp
    rw [e]
    exact h2
  · have e : (m : R) = -((m.natAbs : ℕ) : R) := by
      conv_lhs => rw [h]
      simp
    rw [e]
    exact h2.neg
end Formalism.CohomologicalDescent.DepthNonnegative
