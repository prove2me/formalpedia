-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.good_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:06.846361+00:00
-- url     : https://prove2.me/submissions/d97d8c7f-5c98-4151-8130-fab351647b43

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
theorem _root_.solution {d : ℤ} {c : MvPolynomial (Fin k × Fin k) R} (hc : IsWeightedHomogeneous wt c d) :
    Good wt δ d (Polynomial.C c) := by
  intro i
  rw [Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simpa using hc
  · intro e he
    simp at he
end PI.OddDualWeyl.Hom
