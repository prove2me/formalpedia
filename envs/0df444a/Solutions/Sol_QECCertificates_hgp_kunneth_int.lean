-- Prove2me | solution 1 for QECCertificates.hgp_kunneth_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:19.643862+00:00
-- url     : https://prove2.me/submissions/85e895dc-5b96-4e48-9a90-6da0643d9358

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
public import Theorems.Thm_QECCertificates_rank_hgpHX_add
public import Theorems.Thm_QECCertificates_rank_hgpHZ_add

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
    ((hgpHX A B).rank : ℤ) + ((hgpHZ A B).rank : ℤ)
      + (((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank))
      = (n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂ := by
  have h1 : ((hgpHX A B).rank : ℤ) + (A.rank : ℤ) * B.rank
      = (A.rank : ℤ) * n₂ + (B.rank : ℤ) * r₁ := by
    exact_mod_cast rank_hgpHX_add A B
  have h2 : ((hgpHZ A B).rank : ℤ) + (A.rank : ℤ) * B.rank
      = (A.rank : ℤ) * r₂ + (B.rank : ℤ) * n₁ := by
    exact_mod_cast rank_hgpHZ_add A B
  nlinarith [h1, h2]
end QECCertificates
