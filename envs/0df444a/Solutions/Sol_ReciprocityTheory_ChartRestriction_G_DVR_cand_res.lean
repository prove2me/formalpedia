-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.cand_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:53.708793+00:00
-- url     : https://prove2.me/submissions/fc6dac22-df31-4a85-8ac5-30cab2abb94a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_piece_le_tr
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


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
variable (L φ φ')
variable {L φ ε φ' ε'}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (t : LB.Gen (LB.LinComb L φ ε)) (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) {V : Y.Opens}
    (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ) :
    res hV (cand L φ ε φ' ε' t j' ρ) =
      (∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ * res (hV.trans piece_le_wchart) (t.s (ρ ∘ φ)) := by
  simp only [cand, map_mul, map_inv, map_prod, map_zpow]
  erw [res_res']
  congr 2
  exact Finset.prod_congr rfl fun k' _ => by rw [tr_res L hV (piece_le_tr le_rfl k')]
end ReciprocityTheory.ChartRestriction.G.DVR
