-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectionUnramifiedGeneric_pderiv_inr_rename_inl_3f9f7f18f2dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:45.756274+00:00
-- url     : https://prove2.me/submissions/c9351485-b750-4704-b3bb-2e58cbb79cbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_SplitLinear_RankMinors
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionUnramifiedGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionUnramifiedGeneric

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectionUnramifiedGeneric
namespace GroundTheory.Heights₂.Heights.ProjectionUnramifiedGeneric
theorem _root_.solution {α β : Type} (b : β) (a : MvPolynomial α ℂ) :
    pderiv (Sum.inr b) (rename (Sum.inl : α → α ⊕ β) a) = 0 := by
  classical
  induction a using MvPolynomial.induction_on with
  | C c => simp
  | add p p' hp hp' => simp [hp, hp']
  | mul_X p i hp => simp [pderiv_mul, hp, pderiv_X, Pi.single_apply]
end GroundTheory.Heights₂.Heights.ProjectionUnramifiedGeneric
