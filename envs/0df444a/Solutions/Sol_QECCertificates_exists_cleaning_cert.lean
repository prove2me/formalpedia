-- Prove2me | solution 1 for QECCertificates.exists_cleaning_cert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:56.256972+00:00
-- url     : https://prove2.me/submissions/5cdf820f-d060-476c-90e6-0fe3807ddc49

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_exists_mulVec_of_mem_spanL_colList
public import Theorems.Thm_QECCertificates_preimage_spec
public import Theorems.Thm_QECCertificates_col_decomp
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_spanL_rowReduce
public import Theorems.Thm_QECCertificates_subset_spanL
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.readOff_nil
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)} {ρ : Matrix (Fin r₁) (Fin r₂) (ZMod 2)}
    (hcol : ∀ j, (fun i => ρ i j) ∈ spanL (colList H₁))
    (hrow : ρ * H₂ = 0) :
    ∃ D : Matrix (Fin n₁) (Fin r₂) (ZMod 2), H₁ * D = ρ ∧ D * H₂ = 0 := by
  classical
  have hmem : ∀ ri ∈ rowReduce (colList H₁), ri.1 ∈ spanL (colList H₁) := by
    intro ri hri
    have h1 : ri.1 ∈ spanL (rowList (rowReduce (colList H₁))) :=
      subset_spanL (by rw [rowList]; exact List.mem_map_of_mem hri)
    rwa [spanL_rowReduce] at h1
  refine ⟨Matrix.of fun a j => ∑ ri ∈ (rowReduce (colList H₁)).toFinset,
    ρ ri.2 j * (preimage H₁ ri.1) a, ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ ri ∈ (rowReduce (colList H₁)).toFinset,
        (∑ a, H₁ i a * (ρ ri.2 j * (preimage H₁ ri.1) a)) = ρ ri.2 j * ri.1 i := by
      intro ri hri
      have hpre : H₁ *ᵥ preimage H₁ ri.1 = ri.1 :=
        preimage_spec H₁ (exists_mulVec_of_mem_spanL_colList H₁
          (hmem ri (List.mem_toFinset.mp hri)))
      have hstep : (∑ a, H₁ i a * (ρ ri.2 j * (preimage H₁ ri.1) a))
          = ρ ri.2 j * (H₁ *ᵥ preimage H₁ ri.1) i := by
        rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [hstep, hpre]
    rw [Finset.sum_congr rfl hinner]
    exact (col_decomp ρ (colList H₁) hcol i j).symm
  · ext a t
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ri _ => ?_
    have hstep : (∑ j, (ρ ri.2 j * (preimage H₁ ri.1) a) * H₂ j t)
        = (preimage H₁ ri.1) a * (ρ * H₂) ri.2 t := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hstep, hrow]
    simp
end QECCertificates
