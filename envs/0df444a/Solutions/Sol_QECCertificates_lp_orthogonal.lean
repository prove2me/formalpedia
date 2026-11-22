-- Prove2me | solution 1 for QECCertificates.lp_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:27.120358+00:00
-- url     : https://prove2.me/submissions/52e3ab7a-49d2-462d-9b71-4d1435158393

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_leftMulMat_mul_rightMulMat
public import Theorems.Thm_QECCertificates_lpExpandR_apply
public import Theorems.Thm_QECCertificates_lpExpandL_apply
public import Theorems.Thm_QECCertificates_lpHX_inl
public import Theorems.Thm_QECCertificates_lpHX_inr
public import Theorems.Thm_QECCertificates_lpHZ_inl
public import Theorems.Thm_QECCertificates_lpHZ_inr
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
theorem _root_.solution [Fintype G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (G → ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (G → ZMod 2)) :
    lpHX A B * (lpHZ A B).transpose = 0 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fintype.sum_sum_type,
    lpHX_inl, lpHX_inr, lpHZ_inl, lpHZ_inr]
  have hL : (∑ p : (Fin nA × Fin mB) × G,
        (lpExpandR A (x.1.1, x.2) (p.1.1, p.2) * (if x.1.2 = p.1.2 then 1 else 0)) *
          ((if y.1.1 = p.1.1 then 1 else 0) * lpExpandL B (p.1.2, p.2) (y.1.2, y.2)))
      = ∑ τ : G, leftMulMat (A x.1.1 y.1.1) x.2 τ * rightMulMat (B x.1.2 y.1.2) τ y.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin nA × Fin mB)))
      (f := fun q : Fin nA × Fin mB =>
        (lpExpandR A (x.1.1, x.2) (q.1, τ) * (if x.1.2 = q.2 then 1 else 0)) *
          ((if y.1.1 = q.1 then 1 else 0) * lpExpandL B (q.2, τ) (y.1.2, y.2)))
      (y.1.1, x.1.2) ?_ ?_).trans ?_
    · intro q _ hq
      by_cases h₁ : y.1.1 = q.1
      · by_cases h₂ : x.1.2 = q.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hq
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (y.1.1, x.1.2)) h
    · simp [lpExpandR_apply, lpExpandL_apply]
  have hR : (∑ q : (Fin mA × Fin nB) × G,
        ((if x.1.1 = q.1.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (q.1.2, q.2)) *
          (lpExpandR A (q.1.1, q.2) (y.1.1, y.2) * (if y.1.2 = q.1.2 then 1 else 0)))
      = ∑ τ : G, rightMulMat (B x.1.2 y.1.2) x.2 τ * leftMulMat (A x.1.1 y.1.1) τ y.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin mA × Fin nB)))
      (f := fun q : Fin mA × Fin nB =>
        ((if x.1.1 = q.1 then 1 else 0) * lpExpandL B (x.1.2, x.2) (q.2, τ)) *
          (lpExpandR A (q.1, τ) (y.1.1, y.2) * (if y.1.2 = q.2 then 1 else 0)))
      (x.1.1, y.1.2) ?_ ?_).trans ?_
    · intro q _ hq
      by_cases h₁ : x.1.1 = q.1
      · by_cases h₂ : y.1.2 = q.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hq
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (x.1.1, y.1.2)) h
    · simp [lpExpandR_apply, lpExpandL_apply]
  rw [hL, hR, ← Matrix.mul_apply, ← Matrix.mul_apply, leftMulMat_mul_rightMulMat]
  exact CharTwo.add_self_eq_zero _
end QECCertificates
