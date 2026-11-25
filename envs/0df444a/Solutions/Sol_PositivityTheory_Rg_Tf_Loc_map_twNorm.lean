-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.map_twNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:58.59472+00:00
-- url     : https://prove2.me/submissions/40e1d88a-975b-44b9-9b7e-adfe7ab909ab

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_twNorm_succ
import Theorems.Thm_P2M_PositivityTheory_Rg_Tf_Loc_pow_succ_apply__4aa5921c9ecc

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
theorem _root_.solution (θ : Monoid.End G) (m : ℕ) (δ : G) :
    θ (twNorm θ m δ) = δ⁻¹ * twNorm θ m δ * (θ ^ m) δ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, map_mul, ih, ← pow_succ_apply']
    group
end PositivityTheory.Rg.Tf.Loc
