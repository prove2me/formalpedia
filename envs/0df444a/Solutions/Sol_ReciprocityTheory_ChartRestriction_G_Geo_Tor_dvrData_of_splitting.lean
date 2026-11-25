-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.dvrData_of_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:44.791544+00:00
-- url     : https://prove2.me/submissions/1ad3bdff-3a6c-4222-8a0a-fd68db09f497

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ValPt___ab_adaeffd89a42

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [instance] UnramExt.ring UnramExt.dom UnramExt.dvr UnramExt.alg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (h3 : Y.N3) (P : ValPt Y) (hs : SplitsAt P) : DvrDataAt P := by
  obtain ⟨W, t, m, hsp⟩ := hs
  haveI : CharZero P.K' := P.char0
  haveI : CharZero P.V := (algebraMap P.V P.K').charZero
  haveI : CharZero W.W := ⟨fun a b h => by
    apply Nat.cast_injective (R := P.V)
    apply W.inj
    simpa using h⟩
  exact ⟨W, t, m, hsp, h3 W.W inferInstance inferInstance W.complete (P.ξ W) t m (ValPt.ξ_ab P W) hsp⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
