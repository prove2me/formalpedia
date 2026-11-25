-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPA.opToKT_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:34.069866+00:00
-- url     : https://prove2.me/submissions/75377433-034d-4a64-8748-3d14fa86e0cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPA_opToKT_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.NPA
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
namespace ReciprocityTheory.ChartRestriction.G.T0.NPA
theorem _root_.solution (ϖ : 𝓞 K) :
    OpToKT D N la (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)) =
      algebraMap K (KTf K D N) (ϖ : K) := by
  rw [opToKT_alg, IsScalarTower.algebraMap_apply K (KTp K D N) (KTf K D N), MvPolynomial.algebraMap_eq]
  congr 1
  unfold OTtoKT
  rw [MvPolynomial.map_C]
end ReciprocityTheory.ChartRestriction.G.T0.NPA
