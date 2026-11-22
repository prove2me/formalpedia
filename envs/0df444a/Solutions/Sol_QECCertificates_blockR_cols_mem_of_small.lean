-- Prove2me | solution 1 for QECCertificates.blockR_cols_mem_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:30.169525+00:00
-- url     : https://prove2.me/submissions/5d0076de-b464-4e65-98b5-37d275b0534f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_mem_spanL_of_forall_dot_eq_zero
public import Theorems.Thm_QECCertificates_colDot_hammingNorm_le
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
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
theorem _root_.solution
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hsmall : hammingNorm v < d₂T) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) := by
  rw [colList]
  refine mem_spanL_of_forall_dot_eq_zero H₁.transpose fun w hw => ?_
  by_contra hne
  let y : Vec r₂ := fun t => ∑ i, blockR v i t * w i
  have hy_eq : y = (blockR v).transpose *ᵥ w := rfl
  have hyzero : H₂.transpose *ᵥ y = 0 := by
    rw [hy_eq, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← hcomp, Matrix.transpose_mul,
      ← Matrix.mulVec_mulVec, hw]
    simp
  have hyne : y ≠ 0 := by
    intro hzero
    refine hne ?_
    rw [dotProduct]
    have h1 : y t = 0 := by rw [hzero]; rfl
    exact h1
  have hge : d₂T ≤ hammingNorm y := hd₂ _ hyne hyzero
  have hle : hammingNorm y ≤ hammingNorm v := colDot_hammingNorm_le v w
  omega
end QECCertificates
