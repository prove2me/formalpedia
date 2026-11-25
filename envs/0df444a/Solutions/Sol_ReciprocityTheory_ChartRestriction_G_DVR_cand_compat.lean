-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.cand_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:03:50.168796+00:00
-- url     : https://prove2.me/submissions/e064280f-20b5-41c6-bb48-01f321344395

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_zpow_of_sameSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_g_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_piece_le_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cand_res
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
theorem _root_.solution (hL : L.IsLB) (hs : LB.SameSum φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (j' : K' → L.ι) (ρ ρ₂ : (Y ⟶ X) → L.ι) :
    res (inf_le_left : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (cand L φ ε φ' ε' t j' ρ) =
      res (inf_le_right : (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂) ≤ _)
        (cand L φ ε φ' ε' t j' ρ₂) := by
  set V := (LB.wchart L φ' j' ⊓ piece L φ φ' ρ) ⊓ (LB.wchart L φ' j' ⊓ piece L φ φ' ρ₂)
  rw [cand_res, cand_res]

  have hw : V ≤ LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ (ρ₂ ∘ φ) := fun _ hy => ⟨hy.1.2.1, hy.2.2.1⟩
  have hg := congrArg (res hw) (ht (ρ ∘ φ) (ρ₂ ∘ φ))
  erw [map_mul, res_res', res_res'] at hg
  rw [linComb_g_res L φ ε _ _ hw] at hg
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
  rw [hA, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
