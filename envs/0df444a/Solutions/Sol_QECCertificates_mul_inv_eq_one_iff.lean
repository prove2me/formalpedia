-- Prove2me | solution 1 for QECCertificates.mul_inv_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:08.977038+00:00
-- url     : https://prove2.me/submissions/7cedf2c1-d204-4165-a829-c2fae7ba338f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]
namespace QECCertificates
theorem _root_.solution (σ τ : G) : σ * τ⁻¹ = 1 ↔ σ = τ := by
  constructor
  · intro h
    have h2 : σ * τ⁻¹ * τ = 1 * τ := by rw [h]
    rwa [mul_assoc, inv_mul_cancel, mul_one, one_mul] at h2
  · intro h; rw [h, mul_inv_cancel]
end QECCertificates
