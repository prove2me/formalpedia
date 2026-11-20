-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCoprimeMaximalIdeal_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:50.500523+00:00
-- url     : https://prove2.me/submissions/9b777c91-4de4-40a3-abb5-24919d353e46

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCoprimeMaximalIdeal_ne_bot

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I J : Ideal R) [I.IsMaximal] [J.IsMaximal] (hc : IsCoprime I J) :
    UniqueFactorizationMonoid.normalizedFactors (I*J) = {I} + {J} := by
  have hi := lpsOriginalCoprimeMaximalIdeal_ne_bot I J hc
  have hj := lpsOriginalCoprimeMaximalIdeal_ne_bot J I hc.symm
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hi hj,
    UniqueFactorizationMonoid.normalizedFactors_irreducible
      (Ideal.prime_of_isPrime hi inferInstance).irreducible,
    UniqueFactorizationMonoid.normalizedFactors_irreducible
      (Ideal.prime_of_isPrime hj inferInstance).irreducible,
    normalize_eq,normalize_eq]
end QEC.Coding.TannerLiftedProduct
