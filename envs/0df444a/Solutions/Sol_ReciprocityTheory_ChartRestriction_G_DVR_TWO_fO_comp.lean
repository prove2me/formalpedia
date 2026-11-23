-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TWO.fO_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:05.065785+00:00
-- url     : https://prove2.me/submissions/034a6c39-256f-4949-9759-d6a06552f04b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWO
open ReciprocityTheory.ChartRestriction.G.Out
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  [Algebra (FractionRing V) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TWO
theorem _root_.solution (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) :
    (algebraMap (Ov v) F).comp (fO v hϖ hv) = algVF := rfl
end ReciprocityTheory.ChartRestriction.G.DVR.TWO
