-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.rowGen_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:05:10.051858+00:00
-- url     : https://prove2.me/submissions/01ec9127-a669-4b25-9c6c-14f2b717a92f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_rowGen_diag_X

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
theorem _root_.solution (a : Fin k) {d : ℕ} {f : MvPolynomial (Fin k × Fin k) R}
    (hf : IsWeightedHomogeneous (rowW a) f d) :
    rowGen R a a f = (1 + Polynomial.X) ^ d * Polynomial.C f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (rowW a) m = d := hf (mem_support_iff.mp hm)
  have hC : rowGen R a a (C (coeff m f) : MvPolynomial (Fin k × Fin k) R) = Polynomial.C (C (coeff m f) : MvPolynomial (Fin k × Fin k) R) := by
    simp [rowGen, Polynomial.algebraMap_apply]
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, map_mul, map_prod, hC]
  simp_rw [map_pow, rowGen_diag_X, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul, mul_comm (m _) (rowW a _)]
  ring
end PI.OddDualWeyl.Hom
