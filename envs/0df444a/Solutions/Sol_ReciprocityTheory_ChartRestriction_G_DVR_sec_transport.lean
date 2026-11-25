-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.sec_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:10:01.448401+00:00
-- url     : https://prove2.me/submissions/aaa69ae1-b592-48f9-b6fa-7f001aba6c7e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_glue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_zpow_of_sameSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_g_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_le_iSup_piece
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_piece_le_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_ext_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_candS_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_compat_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_candS_compat

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
theorem _root_.solution (hL : L.IsLB) (hs : LB.SameSum φ ε φ' ε') (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε'), ∀ (j : K → L.ι) (j' : K' → L.ι), LB.Coh L φ j → LB.Coh L φ' j' →
      (∀ k k', φ k = φ' k' → j k = j' k') →
      rs (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (s.f j) =
        rs (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ _) (s'.f j') := by
  have glue : ∀ j' : K' → L.ι, ∃ w : Γ(Y, LB.wchart L φ' j'),
      ∀ ρ, rs (inf_le_left : LB.wchart L φ' j' ⊓ piece L φ φ' ρ ≤ _) w = candS (φ' := φ') (ε' := ε') s j' ρ :=
    fun j' => (sec_glue (LB.wchart L φ' j') (fun ρ => LB.wchart L φ' j' ⊓ piece L φ φ' ρ) (fun _ => inf_le_left)
      (le_iSup_piece L φ φ' hL _) (candS (φ' := φ') (ε' := ε') s j')
      (fun ρ ρ₂ => candS_compat hL hs s j' ρ ρ₂)).exists
  choose w hw using glue
  have hwV : ∀ (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) {V : Y.Opens} (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ),
      rs (hV.trans inf_le_left) (w j') =
        (((∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ : Γ(Y, V)ˣ) : Γ(Y, V)) *
          rs (hV.trans piece_le_wchart) (s.f (ρ ∘ φ)) := by
    intro j' ρ V hV
    rw [← rs_rs (inf_le_left : LB.wchart L φ' j' ⊓ piece L φ φ' ρ ≤ _) hV, hw j' ρ, candS_rs]
  refine ⟨⟨w, ?_⟩, ?_⟩
  · intro (i : K' → L.ι) (j : K' → L.ι)
    show rs _ (w i) = _ * rs _ (w j)
    apply sec_ext_cover _ (fun ρ => (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ)
      (fun _ => inf_le_left) (le_iSup_piece L φ φ' hL _)
    intro ρ
    have hVi : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' i ⊓ piece L φ φ' ρ :=
      fun _ hy => ⟨hy.1.1, hy.2⟩
    have hVj : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' j ⊓ piece L φ φ' ρ :=
      fun _ hy => ⟨hy.1.2, hy.2⟩
    have hV12 : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' i ⊓ LB.wchart L φ' j :=
      fun _ hy => hy.1
    erw [rs_mul, rs_rs, rs_rs, rs_units]
    erw [hwV i ρ hVi, hwV j ρ hVj, linComb_g_res L φ' ε' i j hV12]
    have hcoc : ∀ k', tr L ((LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j k') =
        tr L _ (φ' k') (ρ (φ' k')) (i k') * tr L _ (φ' k') (i k') (j k') := fun k' =>
      (tr_cocycle L hL (fun _ hy => ⟨⟨(piece_le_tr hVi k' hy).1, (piece_le_tr hVi k' hy).2⟩,
        (piece_le_tr hVj k' hy).2⟩)).symm
    have hA : ∏ k', tr L ((LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j k') ^ ε' k' =
        (∏ k', tr L _ (φ' k') (ρ (φ' k')) (i k') ^ ε' k') * ∏ k', tr L _ (φ' k') (i k') (j k') ^ ε' k' := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k' _ => by rw [hcoc k', mul_zpow]
    rw [hA, mul_inv_rev, ← mul_assoc, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  · intro j j' hj hj' hjj'
    apply sec_ext_cover _ (fun ρ => (LB.wchart L φ j ⊓ LB.wchart L φ' j') ⊓ piece L φ φ' ρ)
      (fun _ => inf_le_left) (le_iSup_piece L φ φ' hL _)
    intro ρ
    set O := (LB.wchart L φ j ⊓ LB.wchart L φ' j') ⊓ piece L φ φ' ρ
    have hO' : O ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ := fun _ hy => ⟨hy.1.2, hy.2⟩
    have hOw : O ≤ LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ j := fun _ hy => ⟨hy.2.1, hy.1.1⟩
    erw [rs_rs, rs_rs, hwV j' ρ hO']
    have hg := sec_compat_rs s (ρ ∘ φ) j hOw
    erw [hg]
    let σ : (Y ⟶ X) → L.ι := fun ψ =>
      if h : ∃ k', φ' k' = ψ then j' h.choose else if h₂ : ∃ k, φ k = ψ then j h₂.choose else ρ ψ
    have hσ : ∀ k, σ (φ k) = j k := by
      intro k
      simp only [σ]
      split_ifs with h h₂
      · exact (hjj' k h.choose h.choose_spec.symm).symm
      · exact hj _ _ h₂.choose_spec
      · exact absurd ⟨k, rfl⟩ h₂
    have hσ' : ∀ k', σ (φ' k') = j' k' := by
      intro k'
      simp only [σ]
      rw [dif_pos ⟨k', rfl⟩]
      exact hj' _ _ (⟨k', rfl⟩ : ∃ k₀, φ' k₀ = φ' k').choose_spec
    have hsum : ∏ k, tr L O (φ k) ((ρ ∘ φ) k) (j k) ^ ε k = ∏ k', tr L O (φ' k') (ρ (φ' k')) (j' k') ^ ε' k' := by
      have := prod_zpow_of_sameSum φ ε φ' ε' hs (fun ψ => tr L O ψ (ρ ψ) (σ ψ))
      simp only [hσ, hσ'] at this
      exact this
    rw [hsum, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
end ReciprocityTheory.ChartRestriction.G.DVR
