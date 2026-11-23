-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.algK_unif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:17.060903+00:00
-- url     : https://prove2.me/submissions/ebb316cd-dc5d-4a74-aaca-4d13d7585ff9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) :
    algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) = OpToKT D N la (unifOp D N la) := by
  rw [unifOp, OpToKT, IsLocalization.lift_eq, RingHom.comp_apply, OTtoKT, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply K (KTp K D N) (KTf K D N), MvPolynomial.algebraMap_eq]
end ReciprocityTheory.ChartRestriction.G.T0
