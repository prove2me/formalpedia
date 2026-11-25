-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.rowGen_diag_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:29.030581+00:00
-- url     : https://prove2.me/submissions/6357444d-f02c-4e3a-98ae-acd188debb3e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}
namespace PI.OddDualWeyl.Hom
theorem _root_.solution (a : Fin k) (v : Fin k × Fin k) :
    rowGen R a a (X v) = (1 + Polynomial.X) ^ (rowW a v) * Polynomial.C (X v) := by
  simp only [rowGen, aeval_X, rowW]
  split_ifs with h
  · obtain ⟨v1, v2⟩ := v
    simp only at h ⊢
    subst h
    ring
  · simp
end PI.OddDualWeyl.Hom
