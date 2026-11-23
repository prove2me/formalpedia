-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.twConj_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:42.837929+00:00
-- url     : https://prove2.me/submissions/b85dd3fe-2f3e-41a4-85c0-0ed34799a2e5

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
theorem _root_.solution (θ : Monoid.End G) (δ : G) {h : G} (hh : h ∈ twCent θ δ) (g : G) :
    twConj θ (h * g) δ = twConj θ g δ := by
  have hh' : h⁻¹ * δ * θ h = δ := hh
  simp only [twConj, map_mul]
  rw [show (h * g)⁻¹ * δ * (θ h * θ g) = g⁻¹ * (h⁻¹ * δ * θ h) * θ g by group, hh']
end PositivityTheory.Rg.Tf.Loc
