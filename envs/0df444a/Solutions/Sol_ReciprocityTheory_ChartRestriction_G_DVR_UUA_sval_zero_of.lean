-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.UUA.sval_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:26.436258+00:00
-- url     : https://prove2.me/submissions/7f2ac2d8-bd23-45f3-94ee-02a2ce999ee9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA
theorem _root_.solution {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι)
    (hm : r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k))) : sval s r z J = 0 := by
  have h' := h (fun k => J (r ≫ φ k))
  unfold sval
  rw [h']
  unfold gs
  rw [dif_pos hm]
  erw [map_zero, map_zero]
end ReciprocityTheory.ChartRestriction.G.DVR.UUA
