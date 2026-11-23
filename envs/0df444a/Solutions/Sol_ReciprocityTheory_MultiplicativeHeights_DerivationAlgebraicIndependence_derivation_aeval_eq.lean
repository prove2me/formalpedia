-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:14.286559+00:00
-- url     : https://prove2.me/submissions/cffe54b8-06d6-4f73-a3e7-dd5fe6d9cd9c

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
theorem _root_.solution {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype ι]
    (d : Derivation K R R) (z : ι → R) (P : MvPolynomial ι K) :
    d (aeval z P) = ∑ i, aeval z (pderiv i P) * d (z i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, smul_eq_mul, pderiv_X, Pi.single_apply,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [map_add, map_mul, aeval_X, apply_ite (aeval z), map_zero, map_one, add_mul, mul_ite,
      mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
