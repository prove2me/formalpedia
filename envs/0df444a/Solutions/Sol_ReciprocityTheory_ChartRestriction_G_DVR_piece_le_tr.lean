-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.piece_le_tr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:31.093888+00:00
-- url     : https://prove2.me/submissions/49424423-523d-492f-b1ae-5f1815066832

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
variable {L φ φ'}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {j' : K' → L.ι} {V : Y.Opens} {ρ : (Y ⟶ X) → L.ι} (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ)
    (k' : K') : V ≤ φ' k' ⁻¹ᵁ (L.U (ρ (φ' k')) ⊓ L.U (j' k')) :=
  fun _ hy => ⟨LB.wchart_le L φ' (ρ ∘ φ') k' (hV hy).2.2, LB.wchart_le L φ' j' k' (hV hy).1⟩
end ReciprocityTheory.ChartRestriction.G.DVR
