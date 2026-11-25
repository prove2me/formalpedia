-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthQuotientDet_ord_prod_402dfff309af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:07.650885+00:00
-- url     : https://prove2.me/submissions/4494166e-45b7-4906-ba2e-18ddd3cbb6b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLengthQuotientDet

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
open Module
namespace GroundTheory.Heights₂.Heights
namespace LengthQuotientDet
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] {ι : Type*} (s : Finset ι)
    (a : ι → O) (ha : ∀ i, a i ≠ 0) : Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha j)), ih]
end LengthQuotientDet
end GroundTheory.Heights₂.Heights
