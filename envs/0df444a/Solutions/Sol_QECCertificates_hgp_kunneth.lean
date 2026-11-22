-- Prove2me | solution 1 for QECCertificates.hgp_kunneth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:21.952851+00:00
-- url     : https://prove2.me/submissions/be77650a-421a-487d-8951-f15cc86ee66b

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
public import Theorems.Thm_QECCertificates_hgp_kunneth_int

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
    (n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank - (hgpHZ A B).rank
      = (n₁ - A.rank) * (n₂ - B.rank) + (r₁ - A.rank) * (r₂ - B.rank) := by
  have hA1 : A.rank ≤ n₁ := A.rank_le_width
  have hA2 : A.rank ≤ r₁ := A.rank_le_height
  have hB1 : B.rank ≤ n₂ := B.rank_le_width
  have hB2 : B.rank ≤ r₂ := B.rank_le_height
  have hb : (hgpHX A B).rank + (hgpHZ A B).rank ≤ n₁ * n₂ + r₁ * r₂ := by
    by_contra hcon
    have hlt : ((n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂)
        < ((hgpHX A B).rank : ℤ) + ((hgpHZ A B).rank : ℤ) := by
      exact_mod_cast Nat.not_le.mp hcon
    have h1' : (0 : ℤ) ≤ (n₁ : ℤ) - A.rank := by
      have : (A.rank : ℤ) ≤ (n₁ : ℤ) := by exact_mod_cast hA1
      linarith
    have h2' : (0 : ℤ) ≤ (n₂ : ℤ) - B.rank := by
      have : (B.rank : ℤ) ≤ (n₂ : ℤ) := by exact_mod_cast hB1
      linarith
    have h3' : (0 : ℤ) ≤ (r₁ : ℤ) - A.rank := by
      have : (A.rank : ℤ) ≤ (r₁ : ℤ) := by exact_mod_cast hA2
      linarith
    have h4' : (0 : ℤ) ≤ (r₂ : ℤ) - B.rank := by
      have : (B.rank : ℤ) ≤ (r₂ : ℤ) := by exact_mod_cast hB2
      linarith
    have hnn : (0 : ℤ) ≤ ((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank) := by nlinarith [h1', h2', h3', h4']
    have := hgp_kunneth_int A B
    linarith
  have hle1 : (hgpHX A B).rank ≤ n₁ * n₂ + r₁ * r₂ := le_trans (Nat.le_add_right _ _) hb
  have hle2 : (hgpHZ A B).rank ≤ (n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank := by omega
  apply Nat.cast_injective (R := ℤ)
  have hcast : (((n₁ * n₂ + r₁ * r₂) - (hgpHX A B).rank - (hgpHZ A B).rank : ℕ) : ℤ)
      = (n₁ : ℤ) * n₂ + (r₁ : ℤ) * r₂ - (hgpHX A B).rank - (hgpHZ A B).rank := by
    rw [Nat.cast_sub hle2, Nat.cast_sub hle1]
    push_cast
    ring
  have hcast2 : (((n₁ - A.rank) * (n₂ - B.rank) + (r₁ - A.rank) * (r₂ - B.rank) : ℕ) : ℤ)
      = ((n₁ : ℤ) - A.rank) * ((n₂ : ℤ) - B.rank)
        + ((r₁ : ℤ) - A.rank) * ((r₂ : ℤ) - B.rank) := by
    push_cast [Nat.cast_sub hA1, Nat.cast_sub hA2, Nat.cast_sub hB1, Nat.cast_sub hB2]
    ring
  rw [hcast, hcast2]
  linarith [hgp_kunneth_int A B]
end QECCertificates
