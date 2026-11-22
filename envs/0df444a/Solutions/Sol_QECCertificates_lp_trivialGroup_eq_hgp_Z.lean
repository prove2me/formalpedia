-- Prove2me | solution 1 for QECCertificates.lp_trivialGroup_eq_hgp_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:02.910341+00:00
-- url     : https://prove2.me/submissions/dcbac770-60ac-4ce6-9bc3-0a86d3abcce3

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_lpHZ_liftConst_inl

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]
namespace QECCertificates
theorem _root_.solution [Subsingleton G] [DecidableEq G] {mA nA mB nB : ℕ}
    (A : Matrix (Fin mA) (Fin nA) (ZMod 2)) (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (j : Fin nA) (t : Fin nB) (j' : Fin nA) (s : Fin mB) (σ τ : G) :
    lpHZ (liftConst A) (liftConst B) ((j, t), σ) (Sum.inl ((j', s), τ))
      = hgpHZ A B.transpose (j, t) (Sum.inl (j', s)) := by
  rw [lpHZ_liftConst_inl, if_pos (Subsingleton.elim σ τ), mul_one]
end QECCertificates
