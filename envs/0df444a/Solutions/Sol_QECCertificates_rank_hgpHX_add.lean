-- Prove2me | solution 1 for QECCertificates.rank_hgpHX_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:33.089445+00:00
-- url     : https://prove2.me/submissions/c5caedf9-5055-4869-9477-bd3294edf289

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
public import Theorems.Thm_QECCertificates_range_mulLeft
public import Theorems.Thm_QECCertificates_range_mulRight
public import Theorems.Thm_QECCertificates_hgpHX_mulVecLin_eq_blocks
public import Theorems.Thm_QECCertificates_Matrix_rank_eq_finrank_rowSpace
public import Theorems.Thm_QECCertificates_finrank_colsRows
public import Theorems.Thm_QECCertificates_finrank_colsSub
public import Theorems.Thm_QECCertificates_finrank_rowsSub


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s : ℕ} {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHX A B).rank + A.rank * B.rank = A.rank * n₂ + B.rank * r₁ := by
  have hrange : LinearMap.range (hgpHX A B).mulVecLin
      = LinearMap.range (mulLeft (s := n₂) A) ⊔ LinearMap.range (mulRight (p := r₁) B) := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro X ⟨v, rfl⟩
      rw [hgpHX_mulVecLin_eq_blocks]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨blkL v, rfl⟩)
        (Submodule.mem_sup_right ⟨blkR v, rfl⟩)
    · rintro X ⟨M, rfl⟩
      refine ⟨Sum.elim M (0 : VMat r₁ r₂), ?_⟩
      rw [hgpHX_mulVecLin_eq_blocks]
      have h1 : blkL (Sum.elim M (0 : VMat r₁ r₂)) = M := rfl
      have h2 : blkR (Sum.elim M (0 : VMat r₁ r₂)) = 0 := rfl
      rw [h1, h2, map_zero, add_zero]
    · rintro X ⟨N, rfl⟩
      refine ⟨Sum.elim (0 : VMat n₁ n₂) N, ?_⟩
      rw [hgpHX_mulVecLin_eq_blocks]
      have h1 : blkL (Sum.elim (0 : VMat n₁ n₂) N) = 0 := rfl
      have h2 : blkR (Sum.elim (0 : VMat n₁ n₂) N) = N := rfl
      rw [h1, h2, map_zero, zero_add]
  let L1 : Submodule (ZMod 2) (VMat r₁ n₂) := LinearMap.range (mulLeft (s := n₂) A)
  let L2 : Submodule (ZMod 2) (VMat r₁ n₂) := LinearMap.range (mulRight (p := r₁) B)
  have hL1 : L1 = colsSub (LinearMap.range A.mulVecLin) := range_mulLeft A
  have hL2 : L2 = rowsSub (Matrix.certificateRowSpace B) := range_mulRight B
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) (V := VMat r₁ n₂)
    (s := L1) (t := L2)
  have h1 : Module.finrank (ZMod 2) L1 = A.rank * n₂ := by
    rw [hL1, finrank_colsSub]
    exact mul_comm _ _
  have h2 : Module.finrank (ZMod 2) L2 = B.rank * r₁ := by
    rw [hL2, finrank_rowsSub, ← Matrix.rank_eq_finrank_rowSpace B]
    exact mul_comm _ _
  have h3 : Module.finrank (ZMod 2) ↥(L1 ⊓ L2) = A.rank * B.rank := by
    rw [hL1, hL2, finrank_colsRows, ← Matrix.rank_eq_finrank_rowSpace B]
    rfl
  have hrank : (hgpHX A B).rank = Module.finrank (ZMod 2) ↥(L1 ⊔ L2) := by
    rw [Matrix.rank, hrange]
  rw [hrank]
  rw [h3, h1, h2] at hsup
  exact hsup
end QECCertificates
