-- Prove2me | solution 1 for QECCertificates.kerL_le_spanL_kerBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:28.549999+00:00
-- url     : https://prove2.me/submissions/f0a9369d-b46f-4ca6-a963-6d4a0294d415

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_pivCols
public import Theorems.Thm_QECCertificates_kerVec_apply_free
public import Theorems.Thm_QECCertificates_kerVec_mem_kerL
public import Theorems.Thm_QECCertificates_mem_kerBasis
public import Theorems.Thm_QECCertificates_eq_zero_of_piv_support
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_add_same_left
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_subset_spanL
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


attribute [local simp] QECCertificates.mem_kerL

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) :
    kerL (rowList D) ≤ spanL (kerBasis D) := by
  intro x hx
  rw [mem_kerL] at hx
  set y := ∑ j ∈ Finset.univ.filter (fun j => j ∉ pivCols D), x j • kerVec D j with hy
  have hy_mem : y ∈ spanL (kerBasis D) := by
    rw [hy]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (subset_spanL ?_)
    rw [mem_kerBasis]
    exact ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩
  have hy_ker : y ∈ kerL (rowList D) := by
    rw [hy]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (kerVec_mem_kerL hD j)
  have hxy_ker : ∀ rk ∈ D, rk.1 ⬝ᵥ (x + y) = 0 := by
    intro rk hrk
    have h1 : rk.1 ⬝ᵥ x = 0 := hx rk.1 (List.mem_map_of_mem hrk)
    have h2 : rk.1 ⬝ᵥ y = 0 := by
      rw [mem_kerL] at hy_ker; exact hy_ker rk.1 (List.mem_map_of_mem hrk)
    rw [dotProduct_add, h1, h2, add_zero]
  have hxy_free : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → (x + y) i = 0 := by
    intro i hi
    have hiF : i ∈ Finset.univ.filter (fun j => j ∉ pivCols D) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, by
        rw [mem_pivCols]
        rintro ⟨ri, hri, hcon⟩
        exact hi ri hri hcon⟩
    have hyi : y i = x i := by
      rw [hy, Finset.sum_apply]
      have hsingle : ∑ j ∈ Finset.univ.filter (fun j => j ∉ pivCols D),
            (x j • kerVec D j) i = (x i • kerVec D i) i :=
        Finset.sum_eq_single (s := Finset.univ.filter (fun j => j ∉ pivCols D))
          (f := fun j => (x j • kerVec D j) i) i
          (fun b _ hne => by
            rw [Pi.smul_apply, kerVec_apply_free hi, if_neg (fun h => hne h.symm),
              smul_zero])
          (fun hnot => absurd hiF hnot)
      rw [hsingle, Pi.smul_apply, kerVec_apply_free hi, if_pos rfl, smul_eq_mul,
        mul_one]
    rw [Pi.add_apply, hyi]
    exact CharTwo.add_self_eq_zero (x i)
  have hzero : x + y = 0 := eq_zero_of_piv_support hD hxy_free hxy_ker
  have hxy : x = y := by
    have h := add_add_same_left x y
    rw [hzero, add_zero] at h
    exact h
  rw [hxy]
  exact hy_mem
end QECCertificates
