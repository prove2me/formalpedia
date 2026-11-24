-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_quot_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:23.036802+00:00
-- url     : https://prove2.me/submissions/2bbccd3a-391f-4bad-b9a8-ef47b2564a28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ W.map (algebraMap R (Localization.AtPrime W))) = 1 := by
  rw [Localization.AtPrime.map_eq_maximalIdeal, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom]
  exact Ideal.isMaximal_def.mp inferInstance
end ReciprocityTheory.ChartRestriction.G.AI.I1
