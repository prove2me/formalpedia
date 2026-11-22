-- Prove2me | solution 1 for QECCertificates.hgp_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:58.175372+00:00
-- url     : https://prove2.me/submissions/9ffa637c-1ba1-49e2-9834-e720af01d9b4

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Theorems.Thm_QECCertificates_hgpHX_inl
public import Theorems.Thm_QECCertificates_hgpHX_inr
public import Theorems.Thm_QECCertificates_hgpHZ_inl
public import Theorems.Thm_QECCertificates_hgpHZ_inr
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
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    hgpHX H₁ H₂ * (hgpHZ H₁ H₂).transpose = 0 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fintype.sum_sum_type,
    hgpHX_inl, hgpHX_inr, hgpHZ_inl, hgpHZ_inr]
  have keyL : (∑ p : Fin n₁ × Fin n₂,
        (H₁ x.1 p.1 * (if x.2 = p.2 then 1 else 0)) * ((if y.1 = p.1 then 1 else 0) * H₂ y.2 p.2))
      = H₁ x.1 y.1 * H₂ y.2 x.2 := by
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n₁ × Fin n₂)))
      (f := fun p => (H₁ x.1 p.1 * (if x.2 = p.2 then 1 else 0)) *
        ((if y.1 = p.1 then 1 else 0) * H₂ y.2 p.2)) (y.1, x.2) ?_ ?_).trans ?_
    · intro p _ hp
      by_cases h₁ : y.1 = p.1
      · by_cases h₂ : x.2 = p.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hp
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (y.1, x.2)) h
    · simp
  have keyR : (∑ st : Fin r₁ × Fin r₂,
        ((if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2) * (H₁ st.1 y.1 * (if y.2 = st.2 then 1 else
          0)))
      = H₂ y.2 x.2 * H₁ x.1 y.1 := by
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin r₁ × Fin r₂)))
      (f := fun st => ((if x.1 = st.1 then 1 else 0) * H₂ st.2 x.2) *
        (H₁ st.1 y.1 * (if y.2 = st.2 then 1 else 0))) (x.1, y.2) ?_ ?_).trans ?_
    · intro st _ hst
      by_cases h₁ : x.1 = st.1
      · by_cases h₂ : y.2 = st.2
        · exact absurd (Prod.ext_iff.mpr ⟨h₁.symm, h₂.symm⟩) hst
        · simp [h₂]
      · simp [h₁]
    · intro h
      exact absurd (Finset.mem_univ (x.1, y.2)) h
    · simp
  rw [keyL, keyR]
  have hcomm : H₂ y.2 x.2 * H₁ x.1 y.1 = H₁ x.1 y.1 * H₂ y.2 x.2 := mul_comm _ _
  rw [hcomm]
  exact CharTwo.add_self_eq_zero _
end QECCertificates
