-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.pt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:33.791386+00:00
-- url     : https://prove2.me/submissions/aa8222cd-5147-4d30-8db7-1025b9bd6f33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub

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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
variable {K : Type} [Fintype K] {Y Y' Y'' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {φ'' : K → (Y'' ⟶ X'')}
  {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L' φ' ε)} {t'' : LB.Gen (LB.LinComb L'' φ'' ε)}
  {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (hc : ∀ k, φ'' k ≫ F' = h' ≫ φ' k) (k : K) (y : Y'') : φ' k (h' y) = F' (φ'' k y) := by
  rw [← Scheme.Hom.comp_apply, ← hc k]
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
