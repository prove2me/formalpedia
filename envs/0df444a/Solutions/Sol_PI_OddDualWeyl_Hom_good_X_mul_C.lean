-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.good_X_mul_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:41.025282+00:00
-- url     : https://prove2.me/submissions/ed0ee49c-6e74-4886-b1f9-0ffe673b5c05

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
theorem _root_.solution {d : ℤ} {c : MvPolynomial (Fin k × Fin k) R}
    (hc : IsWeightedHomogeneous wt c (d + δ)) : Good wt δ d (Polynomial.X * Polynomial.C c) := by
  intro i
  rw [Polynomial.X_mul_C, Polynomial.coeff_C_mul_X]
  split_ifs with h
  · subst h
    simpa using hc
  · intro e he
    simp at he
end PI.OddDualWeyl.Hom
