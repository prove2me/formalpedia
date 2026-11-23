-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.coeffDer_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:48.460576+00:00
-- url     : https://prove2.me/submissions/de4a0884-53db-4877-8be9-b574e68c7e1b

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_coeffDer_apply

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
variable {K Ω σ : Type*} [CommRing K] [CommRing Ω] [Algebra K Ω]
namespace ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
theorem _root_.solution (δ : Derivation K Ω Ω) (v : σ) : coeffDer δ (X v : MvPolynomial σ Ω) = 0 := by
  rw [coeffDer_apply]
  show coeffMap δ (monomial (Finsupp.single v 1) 1) = 0
  rw [coeffMap_monomial, Derivation.map_one_eq_zero, map_zero]
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
