-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:02.264273+00:00
-- url     : https://prove2.me/submissions/23d0c10c-1c81-4ecb-8ff0-3b178c314cc9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {K K' U : Type} [Fintype K] [Fintype K'] [CommGroup U] (f : K ⊕ K' → U) {c c' : U}
    (h : ∏ i, f (.inl i) = c) (h' : ∏ i, f (.inr i) = c') : ∏ i, f i = c * c' := by
  rw [Fintype.prod_sum_type, h, h']
end ReciprocityTheory.ChartRestriction.G.DVR
