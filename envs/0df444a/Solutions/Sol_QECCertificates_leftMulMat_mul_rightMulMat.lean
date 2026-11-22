-- Prove2me | solution 1 for QECCertificates.leftMulMat_mul_rightMulMat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:30.780769+00:00
-- url     : https://prove2.me/submissions/ac9649ac-c867-40b2-93b0-4fd2f97855df

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]
namespace QECCertificates
theorem _root_.solution [Fintype G] (a b : G → ZMod 2) :
    leftMulMat a * rightMulMat b = rightMulMat b * leftMulMat a := by
  ext σ τ
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : (∑ ρ, leftMulMat a σ ρ * rightMulMat b ρ τ)
      = ∑ μ, a (σ * μ⁻¹ * τ⁻¹) * b μ := by
    refine Fintype.sum_equiv (mulLeftEquiv τ).symm
      (fun ρ => leftMulMat a σ ρ * rightMulMat b ρ τ)
      (fun μ => a (σ * μ⁻¹ * τ⁻¹) * b μ) ?_
    intro x
    have hx : ((mulLeftEquiv τ).symm) x = τ⁻¹ * x := rfl
    rw [hx]
    simp only [leftMulMat, rightMulMat]
    congr 1
    group
  have hR : (∑ ρ, rightMulMat b σ ρ * leftMulMat a ρ τ)
      = ∑ μ, a (σ * μ⁻¹ * τ⁻¹) * b μ := by
    refine Fintype.sum_equiv (invMulEquiv σ)
      (fun ρ => rightMulMat b σ ρ * leftMulMat a ρ τ)
      (fun μ => a (σ * μ⁻¹ * τ⁻¹) * b μ) ?_
    intro x
    have hx : (invMulEquiv σ) x = x⁻¹ * σ := rfl
    rw [hx]
    simp only [leftMulMat, rightMulMat]
    rw [mul_comm (b (x⁻¹ * σ)) (a (x * τ⁻¹))]
    congr 1
    group
  rw [hL, hR]
end QECCertificates
