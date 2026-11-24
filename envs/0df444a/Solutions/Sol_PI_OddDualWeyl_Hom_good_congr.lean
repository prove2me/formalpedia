-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.good_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:01.952788+00:00
-- url     : https://prove2.me/submissions/b2202f3e-8272-49ad-a0d6-d90a9a15a72c

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
theorem _root_.solution {d e : ℤ} {p : Polynomial (MvPolynomial (Fin k × Fin k) R)} (h : d = e)
    (hp : Good wt δ d p) : Good wt δ e p := by
  subst h
  exact hp
end PI.OddDualWeyl.Hom
