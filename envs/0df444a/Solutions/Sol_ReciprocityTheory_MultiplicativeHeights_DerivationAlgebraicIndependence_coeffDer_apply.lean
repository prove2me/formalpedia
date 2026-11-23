-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.coeffDer_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:06.873264+00:00
-- url     : https://prove2.me/submissions/fc8df574-985c-488a-9fa9-e65c69f51571

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations

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
theorem _root_.solution (δ : Derivation K Ω Ω) (P : MvPolynomial σ Ω) :
    coeffDer δ P = coeffMap δ P := rfl
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
