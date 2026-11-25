-- Prove2me | solution 1 for PI.KerIso.FourSqW.tr_self_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:35.445887+00:00
-- url     : https://prove2.me/submissions/ef5893f9-e687-4ff6-9302-aad063e70f1f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open PI PI.KerIso PI.KerIso.FourSqW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KerIso.FourSqW
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x))
    (x : E) (hx : x ≠ 0) : Algebra.trace K E (x * cj x) ≠ 0 := by
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  intro h
  have := hpos x hx
  rw [← Algebra.trace_trace (S := K), h, map_zero] at this
  exact lt_irrefl _ this
end PI.KerIso.FourSqW
