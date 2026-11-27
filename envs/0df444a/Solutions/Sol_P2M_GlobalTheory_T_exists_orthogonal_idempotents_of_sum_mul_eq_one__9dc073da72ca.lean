-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_orthogonal_idempotents_of_sum_mul_eq_one__9dc073da72ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:34.779049+00:00
-- url     : https://prove2.me/submissions/fb832c07-6b2e-4edf-aebc-bb07dafac0c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsOrthogonalIdempotentsOfSumMulEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsOrthogonalIdempotentsOfSumMulEqOneStatement
import Theorems.Thm_GlobalTheory_AdeleIdempotents_exists_orthogonal_idempotents_of_sum_mul_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (f s : ι → NumberField.AdeleRing (NumberField.RingOfIntegers F) F), ∑ i, s i * f i = 1 → ∃ e t : ι → NumberField.AdeleRing (NumberField.RingOfIntegers F) F, ∑ i, e i = 1 ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ ∀ i, t i * f i = e i := by
  first | exact @GlobalTheory.AdeleIdempotents.exists_orthogonal_idempotents_of_sum_mul_eq_one | exact GlobalTheory.AdeleIdempotents.exists_orthogonal_idempotents_of_sum_mul_eq_one | (intros; apply GlobalTheory.AdeleIdempotents.exists_orthogonal_idempotents_of_sum_mul_eq_one <;> assumption)
end _root_.GlobalTheory.T
