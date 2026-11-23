-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.hasArcData_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:53.240801+00:00
-- url     : https://prove2.me/submissions/17b5240c-1476-4033-a509-b0c9324ae96c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace Model
theorem _root_.solution (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (f : O' →+* R) (u : R) (χ : Sp R ⟶ Y.X) :
    Y.HasArcData a I f u χ ↔ Nonempty (ArcWit Y a I f u χ) :=
  ⟨fun ⟨t, m, P, φ, he, w, e, h⟩ => ⟨⟨t, m, P, φ, he, w, e, h⟩⟩, fun ⟨⟨t, m, P, φ, he, w, e, h⟩⟩ => ⟨t, m, P, φ, he, w, e, h⟩⟩
end Model
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
