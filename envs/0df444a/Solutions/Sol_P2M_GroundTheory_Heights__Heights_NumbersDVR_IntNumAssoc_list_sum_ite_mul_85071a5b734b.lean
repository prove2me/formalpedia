-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_ite_mul_85071a5b734b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:15.144611+00:00
-- url     : https://prove2.me/submissions/9a21a10e-abee-4333-9c09-46a98e3cc9b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumAssoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace IntNumAssoc
theorem _root_.solution {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (c : ℤ) :
    (l.map fun a => if P a then c else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℤ) * c := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih, add_mul]
end IntNumAssoc
end GroundTheory.Heights₂.Heights.NumbersDVR
