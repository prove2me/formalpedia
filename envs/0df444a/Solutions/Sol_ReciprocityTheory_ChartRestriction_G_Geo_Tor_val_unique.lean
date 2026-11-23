-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:51.396363+00:00
-- url     : https://prove2.me/submissions/49fee4c3-32eb-42c7-ac48-ed54863b6015

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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] {X S : Scheme.{0}} (s : X ⟶ S) [IsSeparated s]
    (x x' : Sp R ⟶ X) (h : Out.jK R ≫ x = Out.jK R ≫ x') (h' : x ≫ s = x' ≫ s) : x = x' := by
  obtain ⟨hU, -⟩ : ValuativeCriterion.Uniqueness s ∧ QuasiSeparated s := by
    have : (ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated) s := by
      rw [← IsSeparated.eq_valuativeCriterion]; infer_instance
    exact this
  have hsq : CommSq (Out.jK R ≫ x) (Out.jK R) s (x ≫ s) := ⟨Category.assoc _ _ _⟩
  have hs := hU ⟨R, FractionRing R, Out.jK R ≫ x, x ≫ s, hsq⟩
  exact congrArg CommSq.LiftStruct.l (@Subsingleton.elim _ hs ⟨x, rfl, rfl⟩ ⟨x', h.symm, h'.symm⟩)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
