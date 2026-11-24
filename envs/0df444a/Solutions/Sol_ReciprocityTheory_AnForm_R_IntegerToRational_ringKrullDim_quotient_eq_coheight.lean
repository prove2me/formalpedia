-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.ringKrullDim_quotient_eq_coheight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:52.399514+00:00
-- url     : https://prove2.me/submissions/9756e602-76d9-4be6-835e-eff6516b2423

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace ReciprocityTheory.AnForm.R.IntegerToRational
theorem _root_.solution {A : Type*} [CommRing A] (I : Ideal A) [hI : I.IsPrime] :
    ringKrullDim (A ⧸ I) = (Order.coheight (⟨I, hI⟩ : PrimeSpectrum A) : WithBot ℕ∞) := by
  rw [Order.coheight_eq_krullDim_Ici]
  unfold ringKrullDim
  rw [Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I)]
  exact Order.krullDim_eq_of_orderIso (OrderIso.setCongr _ _ (Set.ext fun p => Iff.rfl))
end ReciprocityTheory.AnForm.R.IntegerToRational
