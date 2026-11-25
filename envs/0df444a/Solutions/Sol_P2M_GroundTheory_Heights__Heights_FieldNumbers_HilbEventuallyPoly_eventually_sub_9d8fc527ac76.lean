-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_eventually_sub_9d8fc527ac76
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:53:15.865548+00:00
-- url     : https://prove2.me/submissions/b3d68d1d-2842-4666-81d7-ce5e05b42238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HilbEventuallyPolyQualified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
theorem _root_.solution {P : (K → ℤ) → Prop} (h : ∀ᶠ m in Filter.atTop, P m) (e : K → ℤ) :
    ∀ᶠ m in Filter.atTop, P (m - e) := by
  rw [Filter.eventually_atTop] at h ⊢
  obtain ⟨a, ha⟩ := h
  refine ⟨a + e, fun b hb => ha _ fun k => ?_⟩
  have := hb k
  simp only [Pi.add_apply] at this
  simp only [Pi.sub_apply]
  linarith
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
