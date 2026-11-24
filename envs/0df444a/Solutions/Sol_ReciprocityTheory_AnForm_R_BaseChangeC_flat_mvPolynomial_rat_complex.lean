-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.BaseChangeC.flat_mvPolynomial_rat_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:52.186677+00:00
-- url     : https://prove2.me/submissions/34854f3e-54f0-4aa5-9d0c-2652700c0514

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.BaseChangeC
open MvPolynomial TensorProduct
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace ReciprocityTheory.AnForm.R.BaseChangeC
theorem _root_.solution :
    Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℚ (MvPolynomial σ ℚ) ℂ (MvPolynomial σ ℂ)
    (Algebra.IsPushout.out (R := ℚ) (S := MvPolynomial σ ℚ) (R' := ℂ) (S' := MvPolynomial σ ℂ))
end ReciprocityTheory.AnForm.R.BaseChangeC
