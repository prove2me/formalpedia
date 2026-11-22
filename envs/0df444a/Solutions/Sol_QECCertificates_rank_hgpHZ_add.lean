-- Prove2me | solution 1 for QECCertificates.rank_hgpHZ_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:29.821495+00:00
-- url     : https://prove2.me/submissions/75e91b24-ab19-4faf-b533-620c7c04d33f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
public import Theorems.Thm_QECCertificates_rank_hgpHX_add
public import Theorems.Thm_QECCertificates_rank_hgpHZ_eq

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
    (hgpHZ A B).rank + A.rank * B.rank = A.rank * r₂ + B.rank * n₁ := by
  have h := rank_hgpHX_add A.transpose B.transpose
  rw [Matrix.rank_transpose, Matrix.rank_transpose] at h
  rw [rank_hgpHZ_eq]
  exact h
end QECCertificates
