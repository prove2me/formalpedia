-- Prove2me | solution 1 for QECCertificates.lp_trivialGroup_eq_hgp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:02.290801+00:00
-- url     : https://prove2.me/submissions/2538a84b-e0a3-47f9-a060-1c6b75a9df35

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_lpHX_liftConst_inl

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]
namespace QECCertificates
theorem _root_.solution [Subsingleton G] [DecidableEq G] {mA nA mB nB : ℕ}
    (A : Matrix (Fin mA) (Fin nA) (ZMod 2)) (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (i : Fin mA) (s : Fin mB) (j : Fin nA) (t : Fin mB) (σ τ : G) :
    lpHX (liftConst A) (liftConst B) ((i, s), σ) (Sum.inl ((j, t), τ))
      = hgpHX A B.transpose (i, s) (Sum.inl (j, t)) := by
  rw [lpHX_liftConst_inl, if_pos (Subsingleton.elim σ τ), mul_one]
end QECCertificates
