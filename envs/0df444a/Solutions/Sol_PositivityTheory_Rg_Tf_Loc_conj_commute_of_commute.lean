-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.conj_commute_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:49.440811+00:00
-- url     : https://prove2.me/submissions/8f68790f-15d1-4965-92a9-12cb93ea7329

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
theorem _root_.solution {x h c : G} (hx : x * (h * c * h⁻¹) = (h * c * h⁻¹) * x) :
    (h⁻¹ * x * h) * c = c * (h⁻¹ * x * h) := by
  calc (h⁻¹ * x * h) * c = h⁻¹ * (x * (h * c * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * c * h⁻¹) * x) * h := by rw [hx]
    _ = c * (h⁻¹ * x * h) := by group
end PositivityTheory.Rg.Tf.Loc
