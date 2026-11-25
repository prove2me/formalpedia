-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.good_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:13.606337+00:00
-- url     : https://prove2.me/submissions/e8ae11e2-d0b6-4c62-97db-121da9ee5df3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_good_congr
import Theorems.Thm_PI_OddDualWeyl_Hom_good_C
import Theorems.Thm_PI_OddDualWeyl_Hom_good_mul
import Theorems.Thm_PI_OddDualWeyl_Hom_good_pow
import Theorems.Thm_PI_OddDualWeyl_Hom_good_prod
import Theorems.Thm_PI_OddDualWeyl_Hom_good_rowGen_X

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
theorem _root_.solution (a b : Fin k) (hδ : ∀ s, wt (a, s) = wt (b, s) + δ) {d : ℤ}
    {f : MvPolynomial (Fin k × Fin k) R} (hf : IsWeightedHomogeneous wt f d) :
    Good wt δ d (rowGen R a b f) := by
  have key : ∀ m ∈ f.support, Good wt δ d (rowGen R a b (monomial m (coeff m f))) := by
    intro m hm
    have hw : Finsupp.weight wt m = d := hf (mem_support_iff.mp hm)
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
    have h1 : Good wt δ 0 (rowGen R a b (C (coeff m f))) := by
      have hC : rowGen R a b (C (coeff m f) : MvPolynomial (Fin k × Fin k) R) = Polynomial.C (C (coeff m f) : MvPolynomial (Fin k × Fin k) R) := by
        simp [rowGen, Polynomial.algebraMap_apply]
      rw [hC]
      exact good_C (isWeightedHomogeneous_C wt _)
    have h2 := good_prod m.support (fun i => rowGen R a b (X i ^ m i)) (fun i => (m i : ℤ) * wt i)
      (fun i _ => by rw [map_pow]; exact good_pow (good_rowGen_X a b hδ i) (m i))
    refine good_congr ?_ (good_mul h1 h2)
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    simp [nsmul_eq_mul]
  rw [f.as_sum, map_sum]
  intro i
  rw [Polynomial.finset_sum_coeff, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_weightedHomogeneousSubmodule]
  exact key m hm i
end PI.OddDualWeyl.Hom
