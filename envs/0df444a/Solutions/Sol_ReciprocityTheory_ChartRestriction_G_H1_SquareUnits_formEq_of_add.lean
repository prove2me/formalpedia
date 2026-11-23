-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.SquareUnits.formEq_of_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:43.890064+00:00
-- url     : https://prove2.me/submissions/e15dba67-000a-4e67-a0cd-d82e4d2587e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TopologicalSpace Opposite
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : ∀ (U : Type) [AddCommGroup U] (h : (Y ⟶ X) → U), ∑ k, ε k • h (φ k) = ∑ k, ε' k • h (φ' k)) :
    FormEq φ ε φ' ε' := by
  intro U _ h
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow] using H (Additive U) (fun ψ => Additive.ofMul (h ψ))
end ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
