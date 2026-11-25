-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.candS_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:13.883023+00:00
-- url     : https://prove2.me/submissions/bc805f99-1473-4a81-bf47-56fe04d43e28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_zpow_of_sameSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_piece_le_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_candS_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_compat_rs

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
theorem _root_.solution (hL : L.IsLB) (hs : LB.SameSum φ ε φ' ε') (s : LB.Sec (LB.LinComb L φ ε))
    (j' : K' → L.ι) (ρ ρ₂ : (Y ⟶ X) → L.ι) :
    rs (inf_le_left : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (candS (φ' := φ') (ε' := ε') s j' ρ) =
      rs (inf_le_right : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (candS (φ' := φ') (ε' := ε') s j' ρ₂) := by
  set V := (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂)
  rw [candS_rs, candS_rs]
  have hw : V ≤ LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ (ρ₂ ∘ φ) := fun _ hy => ⟨hy.1.2.1, hy.2.2.1⟩
  have hg := sec_compat_rs s (ρ ∘ φ) (ρ₂ ∘ φ) hw
  erw [hg]
  have hsum : ∏ k, tr L V (φ k) ((ρ ∘ φ) k) ((ρ₂ ∘ φ) k) ^ ε k =
      ∏ k', tr L V (φ' k') (ρ (φ' k')) (ρ₂ (φ' k')) ^ ε' k' :=
    prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => tr L V ψ (ρ ψ) (ρ₂ ψ))
  rw [hsum]
  have hcoc : ∀ k', tr L V (φ' k') (ρ (φ' k')) (j' k') =
      tr L V (φ' k') (ρ (φ' k')) (ρ₂ (φ' k')) * tr L V (φ' k') (ρ₂ (φ' k')) (j' k') := fun k' =>
    (tr_cocycle L hL (fun _ hy => ⟨⟨(piece_le_tr inf_le_left k' hy).1, (piece_le_tr inf_le_right k' hy).1⟩,
      (piece_le_tr inf_le_left k' hy).2⟩)).symm
  have hA : ∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k' =
      (∏ k', tr L V (φ' k') (ρ (φ' k')) (ρ₂ (φ' k')) ^ ε' k') *
        ∏ k', tr L V (φ' k') (ρ₂ (φ' k')) (j' k') ^ ε' k' := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k' _ => by rw [hcoc k', mul_zpow]
  rw [hA, mul_inv_rev, ← mul_assoc, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]
end ReciprocityTheory.ChartRestriction.G.DVR
