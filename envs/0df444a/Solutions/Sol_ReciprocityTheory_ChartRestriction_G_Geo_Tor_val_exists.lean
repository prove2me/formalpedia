-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:54.100638+00:00
-- url     : https://prove2.me/submissions/d7663154-8395-4fc8-b800-78692e69ce59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc

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
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s]
    (y : Sp (FractionRing R) ⟶ X) (r : Sp R ⟶ S) (h : y ≫ s = Out.jK R ≫ r) :
    ∃ x : Sp R ⟶ X, Out.jK R ≫ x = y ∧ x ≫ s = r := by
  obtain ⟨hE, -⟩ : ValuativeCriterion.Existence s ∧ QuasiCompact s := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact this
  obtain ⟨⟨l⟩⟩ := hE ⟨R, FractionRing R, y, r, ⟨h⟩⟩
  exact ⟨l.l, l.fac_left, l.fac_right⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
