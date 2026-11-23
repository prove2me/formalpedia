-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.disj_intS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:38.871552+00:00
-- url     : https://prove2.me/submissions/9947dbf8-39cb-4d8b-ae82-ed291691c75b

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
theorem _root_.solution (P : Ideal (MvPolynomial σ ℤ)) (hP : ChZero P) :
    Disjoint ((intS σ : Submonoid _) : Set (MvPolynomial σ ℤ)) (P : Set _) := by
  rw [Set.disjoint_left]
  rintro _ ⟨m, hm, rfl⟩ hmP
  exact nonZeroDivisors.ne_zero hm (hP m hmP)
end ReciprocityTheory.AnForm.R.IntegerToRational
