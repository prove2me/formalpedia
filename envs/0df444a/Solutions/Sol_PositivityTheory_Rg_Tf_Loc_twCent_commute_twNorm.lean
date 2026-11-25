-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.twCent_commute_twNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:22.45549+00:00
-- url     : https://prove2.me/submissions/fcf34740-e11d-42e5-ac3f-6691c2c7731e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_twNorm_twConj_of_pow_eq_one

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
theorem _root_.solution (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) (δ : G) {g : G}
    (hg : g ∈ twCent θ δ) : g * twNorm θ ℓ δ = twNorm θ ℓ δ * g := by
  have h1 := twNorm_twConj_of_pow_eq_one θ hℓ g δ
  have hg' : twConj θ g δ = δ := hg
  rw [hg'] at h1
  calc g * twNorm θ ℓ δ = g * (g⁻¹ * twNorm θ ℓ δ * g) := by rw [← h1]
    _ = twNorm θ ℓ δ * g := by group
end PositivityTheory.Rg.Tf.Loc
