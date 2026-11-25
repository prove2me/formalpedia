-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.twNorm_twConj_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:09:53.313931+00:00
-- url     : https://prove2.me/submissions/8798138e-c5ac-4e13-8f75-f0e468b6d70a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_twNorm_twConj

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
theorem _root_.solution (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) (g δ : G) :
    twNorm θ ℓ (twConj θ g δ) = g⁻¹ * twNorm θ ℓ δ * g := by
  rw [twNorm_twConj, hℓ]; rfl
end PositivityTheory.Rg.Tf.Loc
