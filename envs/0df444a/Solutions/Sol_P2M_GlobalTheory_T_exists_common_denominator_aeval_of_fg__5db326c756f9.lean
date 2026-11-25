-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_common_denominator_aeval_of_fg__5db326c756f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:11.665484+00:00
-- url     : https://prove2.me/submissions/6e265ad7-4dd1-44f6-8ceb-b910b9179b8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFgStatement
import Theorems.Thm_GlobalTheory_exists_common_denominator_aeval_of_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A), (∀ x : A, ∃ p : E[X], aeval g p = x) → ∀ S : Submodule O A, S.FG → ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  first | exact @GlobalTheory.exists_common_denominator_aeval_of_fg | exact GlobalTheory.exists_common_denominator_aeval_of_fg | (intros; apply GlobalTheory.exists_common_denominator_aeval_of_fg <;> assumption)
end _root_.GlobalTheory.T
