-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_valU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:10:52.459822+00:00
-- url     : https://prove2.me/submissions/1fed6136-a3e5-4cad-9dc9-3c85afdd5b0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
section Units
variable {Z Z' : Scheme.{0}}
private lemma ringHom_units_zpow_lemma {R S : Type*} [CommRing R] [Field S] (f : R →+* S) (u : Rˣ) (k : ℤ) :
    f ↑(u ^ k) = (f ↑u) ^ k := by
  have hk : ((Units.map (f : R →* S) (u ^ k) : Sˣ) : S) = ((Units.map (f : R →* S) u ^ k : Sˣ) : S) := by
    rw [map_zpow]
  rw [Units.val_zpow_eq_zpow_val] at hk
  exact hk
end Units
section Rd
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}
end Rd
end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {Z Z' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (p : Sp ℂ ⟶ Z) {V : Z.Opens} (h : ⊤ ≤ p ⁻¹ᵁ V) (u : Γ(Z, V)ˣ) (k : ℤ) :
    valAt' p V ((u ^ k : Γ(Z, V)ˣ) : Γ(Z, V)) = valAt' p V (u : Γ(Z, V)) ^ k := by
  rw [valAt', valAt', dif_pos h, dif_pos h]
  delta valAt
  exact ringHom_units_zpow_lemma ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (p.appLE V ⊤ h).hom) u k
end ReciprocityTheory.ChartRestriction.G.PullbackSections
