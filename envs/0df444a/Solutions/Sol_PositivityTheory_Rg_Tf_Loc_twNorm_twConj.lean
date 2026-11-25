-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.twNorm_twConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:43.94007+00:00
-- url     : https://prove2.me/submissions/a7a1ee8c-0229-45c5-8933-88a1d17efa11

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_twNorm_succ
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_pow_succ_apply

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
theorem _root_.solution (θ : Monoid.End G) (m : ℕ) (g δ : G) :
    twNorm θ m (twConj θ g δ) = g⁻¹ * twNorm θ m δ * (θ ^ m) g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, twNorm_succ, ih, twConj, map_mul, map_mul, map_inv, pow_succ_apply θ m g]
    group
end PositivityTheory.Rg.Tf.Loc
