-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.le_iSup_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:25.174332+00:00
-- url     : https://prove2.me/submissions/562b6115-a346-4517-9d31-2d884c3b9be3

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
variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hL : L.IsLB) (W : Y.Opens) : W ≤ ⨆ ρ, W ⊓ piece L φ φ' ρ := by
  intro y hy
  have hex : ∀ ψ : Y ⟶ X, ∃ i, ψ.base y ∈ L.U i := fun ψ => by
    have : ψ.base y ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  choose ρ hρ using hex
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨ρ, hy, Set.mem_iInter.2 fun k => hρ (φ k),
    Set.mem_iInter.2 fun k => hρ (φ' k)⟩
end ReciprocityTheory.ChartRestriction.G.DVR
