-- Prove2me | solution 1 for QECCertificates.inv_mul_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:22.507599+00:00
-- url     : https://prove2.me/submissions/88d279af-aff9-4e39-89b9-f97fd8ec0447

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
theorem _root_.solution (σ τ : G) : τ⁻¹ * σ = 1 ↔ σ = τ := by
  constructor
  · intro h
    have h2 : τ * (τ⁻¹ * σ) = τ * 1 := by rw [h]
    rwa [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
  · intro h; rw [h, inv_mul_cancel]
end QECCertificates
