-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.comap_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:33.387234+00:00
-- url     : https://prove2.me/submissions/45d421ae-7916-4322-a2cf-efd08da1c329

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_disj_intS

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
theorem _root_.solution (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : ChZero P) :
    (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) = P := by
  have hA : algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  rw [← hA]
  exact IsLocalization.under_map_of_isPrime_disjoint (intS σ) (MvPolynomial σ ℚ) ‹_› (disj_intS P hP)
end ReciprocityTheory.AnForm.R.IntegerToRational
