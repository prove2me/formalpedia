-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_X_59eac33e54da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:40.045085+00:00
-- url     : https://prove2.me/submissions/bf2d5c7b-16a9-4abd-9e06-22ae08e0baf3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSymmetricSpanHsymm

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
open MvPolynomial Finset
open GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
omit [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
theorem _root_.solution (t : Multiset σ) :
    ((t.map (X : σ → MvPolynomial σ ℤ)).prod).IsHomogeneous (Multiset.card t) := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
    exact (isHomogeneous_X ℤ a).mul ih
end GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
