-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:08.179855+00:00
-- url     : https://prove2.me/submissions/d55193a7-ee8e-4897-bd9f-206dfe894746

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_add_0410d0a13fef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_zero_8589bd36c748

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
namespace IsAlt
theorem _root_.solution {ι : Type*} (s : Finset ι) {P : ι → MvPolynomial (Fin m) ℚ}
    (hP : ∀ i ∈ s, IsAlt (P i)) : IsAlt (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsAlt.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hP a (mem_insert_self a s)).add (ih fun i hi => hP i (mem_insert_of_mem hi))
end IsAlt
end GroundTheory.Heights₂.Heights.RestTerms.Comb
