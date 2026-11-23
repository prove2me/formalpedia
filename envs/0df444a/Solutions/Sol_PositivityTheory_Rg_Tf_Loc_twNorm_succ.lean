-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.twNorm_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:17.374041+00:00
-- url     : https://prove2.me/submissions/82529ff1-5bda-439a-9c33-84e14bcd4340

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL

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
    twNorm θ (m + 1) δ = twNorm θ m δ * (θ ^ m) δ := by
  simp [twNorm, List.range_succ, List.prod_append]
end PositivityTheory.Rg.Tf.Loc
