-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.map_twNorm_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:12.594283+00:00
-- url     : https://prove2.me/submissions/eb3fd68a-e7d7-4203-8038-1f1725a74fa7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_map_twNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Tf PositivityTheory.Rg.Tf.Loc
noncomputable section
variable {G : Type*} [Group G]
namespace PositivityTheory.Rg.Tf.Loc
theorem _root_.solution (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) (δ : G) :
    θ (twNorm θ ℓ δ) = δ⁻¹ * twNorm θ ℓ δ * δ := by
  rw [map_twNorm, hℓ]; rfl
end PositivityTheory.Rg.Tf.Loc
