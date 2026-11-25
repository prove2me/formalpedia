-- Prove2me | solution 1 for PI.UnitKronW.map_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:07.468939+00:00
-- url     : https://prove2.me/submissions/953e28b0-fb5b-4dc2-a9ca-ac1cce971803

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitKron
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitKronecker_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitKronW
open Matrix Polynomial ComplexOrder
namespace PI.UnitKronW
theorem _root_.solution {E : Type} [Field E] (c : E →+* E) (φ : E →+* ℂ)
    (hc : ∀ x : E, φ (c x) = (starRingEnd ℂ) (φ x)) {k : ℕ} (J γ : Matrix (Fin k) (Fin k) E)
    (hγ : (γ.map c)ᵀ * J * γ = J) : (γ.map φ)ᴴ * J.map φ * γ.map φ = J.map φ := by
  have h := congrArg (fun M => M.map φ) hγ
  simp only [Matrix.map_mul] at h
  convert h using 3
  ext i j
  simp [Matrix.conjTranspose_apply, hc, Complex.star_def]
end PI.UnitKronW
