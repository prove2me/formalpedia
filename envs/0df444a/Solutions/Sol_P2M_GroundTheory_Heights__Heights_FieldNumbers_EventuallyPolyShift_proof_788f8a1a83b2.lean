-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_EventuallyPolyShift_proof_788f8a1a83b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:33.024338+00:00
-- url     : https://prove2.me/submissions/52cf6d92-d075-413f-b606-ffd70a723975

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PEventuallyPolyShift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_bind__le_of_le_one_a3d3ab82f1c0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace EventuallyPolyShift
theorem _root_.solution : EventuallyPolyShift.Statement := by
  intro K _ h p c hp
  refine ⟨bind₁ (fun k => X k - C (c k : ℚ)) p, ?_, ?_, ?_⟩
  · have ht : Tendsto (fun m : K → ℤ => m + -c) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-c) tendsto_id
    refine (ht.eventually hp).mono fun m hm => ?_
    simp only [← sub_eq_add_neg] at hm
    have e := eval₂Hom_bind₁ (RingHom.id ℚ) (fun k => (m k : ℚ)) (fun k => X k - C (c k : ℚ)) p
    rw [hm]
    refine Eq.trans ?_ e.symm
    show eval _ p = eval _ p
    refine congrArg (fun x => eval x p) (funext fun k => ?_)
    simp
  · exact totalDegree_bind₁_le_of_le_one _
      (fun k => (totalDegree_sub_C_le _ _).trans (totalDegree_X k).le) p
  · rintro rfl
    exact map_zero _
end EventuallyPolyShift
end GroundTheory.Heights₂.Heights.FieldNumbers
