-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.mem_twCent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:38.466825+00:00
-- url     : https://prove2.me/submissions/800214ec-8dda-47de-8bb1-ff9d28ff8dc2

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
theorem _root_.solution (θ : Monoid.End G) (δ g : G) : g ∈ twCent θ δ ↔ g⁻¹ * δ * θ g = δ := Iff.rfl
end PositivityTheory.Rg.Tf.Loc
