-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_hsymm_int_5d930b32fefa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:23.238931+00:00
-- url     : https://prove2.me/submissions/d5397cb5-ce2a-4b3e-881a-2a2a67ddbfa5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSymmetricSpanHsymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_X_59eac33e54da

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
theorem _root_.solution (a : ℕ) : (hsymm σ ℤ a).IsHomogeneous a := by
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  have := isHomogeneous_prod_map_X (σ := σ) s.1
  rwa [s.2] at this
end GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
