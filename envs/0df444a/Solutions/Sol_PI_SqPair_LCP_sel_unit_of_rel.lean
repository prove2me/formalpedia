-- Prove2me | solution 1 for PI.SqPair.LCP.sel_unit_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:22:55.015895+00:00
-- url     : https://prove2.me/submissions/bd01405c-2d6c-4d97-953c-63f0d398d643

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SelCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [IsDomain R]
namespace PI.SqPair.LCP
theorem _root_.solution (σ : R ≃+* R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' h₁ : Matrix ι ι R) (hA' : IsUnit A'.det)
    (hrel : (h₁.map σ)ᵀ * A * h₁ = A') : IsUnit h₁.det := by
  have e := congrArg Matrix.det hrel
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hA'
  exact isUnit_of_mul_isUnit_right hA'
end PI.SqPair.LCP
