-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.mem_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:13.009543+00:00
-- url     : https://prove2.me/submissions/c2b7a684-e0a8-4901-948a-98efb7105e69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) (x : E) :
    x ∈ vRing v ↔ 0 ≤ v x :=
  (Valuation.mem_valuationSubring_iff (v : Valuation E (Multiplicative (WithTop ℤ)ᵒᵈ)) x).trans Iff.rfl
end ReciprocityTheory.ChartRestriction.G.T0
