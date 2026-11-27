-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.conj_twCent_mem_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:20:55.387086+00:00
-- url     : https://prove2.me/submissions/25615ae5-5667-496d-aef3-6c9a0989f4c2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_twCent_commute_twNorm
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_conj_commute_of_commute

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
theorem _root_.solution (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) {δ h c : G}
    (hN : twNorm θ ℓ δ = h * c * h⁻¹) {x : G} (hx : x ∈ twCent θ δ) :
    h⁻¹ * x * h ∈ Subgroup.centralizer ({c} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := twCent_commute_twNorm θ hℓ δ hx
  rw [hN] at this
  exact conj_commute_of_commute this
end PositivityTheory.Rg.Tf.Loc
