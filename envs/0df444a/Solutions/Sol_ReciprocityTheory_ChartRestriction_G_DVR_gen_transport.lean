-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gen_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:49.169633+00:00
-- url     : https://prove2.me/submissions/d6088540-b3c1-418a-991d-dab32d4f685a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_units_glue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_zpow_of_sameSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_g_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_le_iSup_piece
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_piece_le_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cand_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cand_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_units_ext_cover
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
theorem _root_.solution (hL : L.IsLB) (hs : LB.SameSum φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε'), t'.IsGen ∧ LB.Gen.Corr L φ ε φ' ε' t t' := by
  have glue : ∀ j' : K' → L.ι, ∃ w : Γ(Y, LB.wchart L φ' j')ˣ,
      ∀ ρ, res (inf_le_left : LB.wchart L φ' j' ⊓ piece L φ φ' ρ ≤ _) w = cand L φ ε φ' ε' t j' ρ :=
    fun j' => units_glue (LB.wchart L φ' j') (fun ρ => LB.wchart L φ' j' ⊓ piece L φ φ' ρ) (fun _ => inf_le_left)
      (le_iSup_piece L φ φ' hL _) (cand L φ ε φ' ε' t j') (fun ρ ρ₂ => cand_compat hL hs t ht j' ρ ρ₂)
  choose w hw using glue

  have hwV : ∀ (j' : K' → L.ι) (ρ : (Y ⟶ X) → L.ι) {V : Y.Opens} (hV : V ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ),
      res (hV.trans inf_le_left) (w j') =
        (∏ k', tr L V (φ' k') (ρ (φ' k')) (j' k') ^ ε' k')⁻¹ * res (hV.trans piece_le_wchart) (t.s (ρ ∘ φ)) := by
    intro j' ρ V hV
    rw [← res_res' (inf_le_left : LB.wchart L φ' j' ⊓ piece L φ φ' ρ ≤ _) hV, hw j' ρ, cand_res]
  refine ⟨⟨w⟩, ?_, ?_⟩
  ·
    intro (i : K' → L.ι) (j : K' → L.ι)
    show res _ (w i) = _ * res _ (w j)
    apply units_ext_cover _ (fun ρ => (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ)
      (fun _ => inf_le_left) (le_iSup_piece L φ φ' hL _)
    intro ρ
    have hVi : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' i ⊓ piece L φ φ' ρ :=
      fun _ hy => ⟨hy.1.1, hy.2⟩
    have hVj : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' j ⊓ piece L φ φ' ρ :=
      fun _ hy => ⟨hy.1.2, hy.2⟩
    erw [map_mul, res_res', res_res']
    have hV12 : (LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ ≤ LB.wchart L φ' i ⊓ LB.wchart L φ' j :=
      fun _ hy => hy.1
    erw [hwV i ρ hVi, hwV j ρ hVj, linComb_g_res L φ' ε' i j hV12]
    have hcoc : ∀ k', tr L ((LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j k') =
        tr L _ (φ' k') (ρ (φ' k')) (i k') * tr L _ (φ' k') (i k') (j k') := fun k' =>
      (tr_cocycle L hL (fun _ hy => ⟨⟨(piece_le_tr hVi k' hy).1, (piece_le_tr hVi k' hy).2⟩,
        (piece_le_tr hVj k' hy).2⟩)).symm
    have hA : ∏ k', tr L ((LB.wchart L φ' i ⊓ LB.wchart L φ' j) ⊓ piece L φ φ' ρ) (φ' k') (ρ (φ' k')) (j k') ^ ε' k' =
        (∏ k', tr L _ (φ' k') (ρ (φ' k')) (i k') ^ ε' k') * ∏ k', tr L _ (φ' k') (i k') (j k') ^ ε' k' := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k' _ => by rw [hcoc k', mul_zpow]
    rw [hA, mul_inv_rev, ← mul_assoc, mul_inv_cancel_left]
  ·
    intro j j' hj hj' hjj'
    apply units_ext_cover _ (fun ρ => (LB.wchart L φ j ⊓ LB.wchart L φ' j') ⊓ piece L φ φ' ρ)
      (fun _ => inf_le_left) (le_iSup_piece L φ φ' hL _)
    intro ρ
    set O := (LB.wchart L φ j ⊓ LB.wchart L φ' j') ⊓ piece L φ φ' ρ
    have hO' : O ≤ LB.wchart L φ' j' ⊓ piece L φ φ' ρ := fun _ hy => ⟨hy.1.2, hy.2⟩
    have hOw : O ≤ LB.wchart L φ (ρ ∘ φ) ⊓ LB.wchart L φ j := fun _ hy => ⟨hy.2.1, hy.1.1⟩
    erw [res_res', res_res', hwV j' ρ hO']
    have hg := congrArg (res hOw) (ht (ρ ∘ φ) j)
    erw [map_mul, res_res', res_res'] at hg
    rw [linComb_g_res L φ ε _ _ hOw] at hg
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
    rw [hsum, inv_mul_cancel_left]
    rfl
end ReciprocityTheory.ChartRestriction.G.DVR
