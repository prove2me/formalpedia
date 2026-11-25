-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_eq_zero_of_forall_psi_85d62bcfb82e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:20.754024+00:00
-- url     : https://prove2.me/submissions/cd3584cf-74c6-4544-ad54-d4f6e221d527

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic

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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.KRest
theorem _root_.solution {t : ℝ} (h : ∀ ψ : ℝ →ₗ[ℚ] ℚ, ψ t = 0) : t = 0 :=
  (Module.forall_dual_apply_eq_zero_iff ℚ t).mp h
end GroundTheory.Heights₂.Heights.KRest
