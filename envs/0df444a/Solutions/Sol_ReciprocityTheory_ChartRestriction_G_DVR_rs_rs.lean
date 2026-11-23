-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.rs_rs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:20.3201+00:00
-- url     : https://prove2.me/submissions/79c67cb6-1535-4f30-931a-9f4f2d2fb2a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Z : Scheme.{0}} {U W V : Z.Opens} (h : W ≤ U) (h' : V ≤ W) (x : Γ(Z, U)) :
    rs h' (rs h x) = rs (h'.trans h) x := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
