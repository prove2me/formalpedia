-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.isUnit_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:22.036804+00:00
-- url     : https://prove2.me/submissions/b0a56a76-2712-43e1-a7cb-242d90dc32e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_NuExtA

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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (p : X ⟶ Sp V) (x : X) {r : V} (hx : r ∉ (p x).asIdeal) : IsUnit (cst p x r) := by
  have hmem : p x ∈ (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) := by
    have e := basicOpen_eq_of_affine (R := CommRingCat.of V) r
    exact (congrArg (fun U : (Sp V).Opens => p x ∈ U) e).mpr hx
  have e2 := Scheme.preimage_basicOpen p ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)
  have hx' : x ∈ X.basicOpen ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)) := by
    rw [← e2]; exact hmem
  have hu := (Scheme.mem_basicOpen X ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)) x
    (show x ∈ p ⁻¹ᵁ ⊤ from trivial)).1 hx'
  rw [cst, gs_eq p x ⊤ (show p x ∈ (⊤ : (Sp V).Opens) from trivial)]
  exact hu
end ReciprocityTheory.ChartRestriction.G.DVR
