-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:00.619019+00:00
-- url     : https://prove2.me/submissions/fbd2a148-8a32-458e-bba3-82e658ece71c

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
theorem _root_.solution {d e : ℤ} {p q : Polynomial (MvPolynomial (Fin k × Fin k) R)}
    (hp : Good wt δ d p) (hq : Good wt δ e q) : Good wt δ (d + e) (p * q) := by
  intro i
  rw [Polynomial.coeff_mul, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [mem_weightedHomogeneousSubmodule]
  have h := (hp x.1).mul (hq x.2)
  convert h using 1
  rw [← hx]
  push_cast
  ring
end PI.OddDualWeyl.Hom
