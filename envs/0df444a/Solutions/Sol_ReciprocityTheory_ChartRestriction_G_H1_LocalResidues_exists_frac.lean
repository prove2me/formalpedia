-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.LocalResidues.exists_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:12.798858+00:00
-- url     : https://prove2.me/submissions/1979ec17-b48d-4b68-a465-3134efd6a553

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_LocalResidues
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_stalkMap


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {k : Type} [Field k] {X W Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
theorem _root_.solution (h0 : X ⟶ W) [IsIso h0] (D : W.Opens) (hD : IsAffineOpen D) (y : X) (hy : h0 y ∈ D)
    (f : X.presheaf.stalk y) :
    ∃ g g' : Γ(W, D), IsUnit (gs h0 y D g') ∧ f * gs h0 y D g' = gs h0 y D g := by
  have hiso : IsIso (h0.stalkMap y) := ((isIso_iff_isIso_stalkMap h0).1 inferInstance).2 y
  obtain ⟨f0, rfl⟩ := (ConcreteCategory.bijective_of_isIso (h0.stalkMap y)).2 f
  let _ : Algebra Γ(W, D) (W.presheaf.stalk (h0 y)) := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨h0 y, hy⟩
  have := hD.isLocalization_stalk ⟨h0 y, hy⟩
  obtain ⟨⟨g, g'⟩, hmk⟩ := IsLocalization.mk'_surjective (hD.primeIdealOf ⟨h0 y, hy⟩).asIdeal.primeCompl f0
  have hmk' : IsLocalization.mk' (W.presheaf.stalk (h0 y)) g g' = f0 := hmk
  have hspec := IsLocalization.mk'_spec (W.presheaf.stalk (h0 y)) g g'
  have hunit := IsLocalization.map_units (W.presheaf.stalk (h0 y)) g'
  have ge : ∀ a : Γ(W, D), gs h0 y D a = (h0.stalkMap y).hom (algebraMap Γ(W, D) (W.presheaf.stalk (h0 y)) a) :=
    fun a => (gs_stalkMap h0 y D hy a).trans (congrArg _ (gs_eq (𝟙 W) (h0 y) D hy a))
  refine ⟨g, g'.1, ?_, ?_⟩
  · rw [ge]; exact hunit.map _
  · rw [ge, ge, ← map_mul, ← hmk', hspec]
end ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
