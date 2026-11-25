-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumAssoc_list_sum_ite_enat_5414286079ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:14.47081+00:00
-- url     : https://prove2.me/submissions/499c32bf-5b8f-417c-a288-711a30313d09

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
theorem _root_.solution {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] :
    (l.map fun a => if P a then (1 : ℕ∞) else 0).sum =
      ((l.map fun a => if P a then (1 : ℕ) else 0).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]
end IntNumAssoc
end GroundTheory.Heights₂.Heights.NumbersDVR
