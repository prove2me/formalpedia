-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.candS_rs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:53.192786+00:00
-- url     : https://prove2.me/submissions/dbb2a0fb-0c45-4eea-8b4e-f238ce558db6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_piece_le_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul

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
theorem _root_.solution (s : LB.Sec (LB.LinComb L φ ε)) (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) {V : Y.Opens}
    (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ) :
    rs hV (candS (φ' := φ') (ε' := ε') s j' ρ) =
      (((∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ : Γ(Y, V)ˣ) : Γ(Y, V)) *
        rs (hV.trans piece_le_wchart) (s.f (ρ ∘ φ)) := by
  unfold candS
  rw [rs_mul, rs_units]
  congr 1
  · congr 1
    simp only [map_inv, map_prod, map_zpow]
    congr 1
    exact Finset.prod_congr rfl fun k' _ => by rw [tr_res L hV (piece_le_tr le_rfl k')]
  · exact rs_rs _ _ _
end ReciprocityTheory.ChartRestriction.G.DVR
