-- Prove2me | solution 1 for QECCertificates.blockL_rows_mem_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:26.225821+00:00
-- url     : https://prove2.me/submissions/8b71f7b0-43ac-43ea-9b31-d2d5e6751937

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_mem_spanL_of_forall_dot_eq_zero
public import Theorems.Thm_QECCertificates_rowDot_hammingNorm_le
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
    (hcomp : H₁ * blockL v = blockR v * H₂) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hsmall : hammingNorm v < d₁) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) := by
  refine mem_spanL_of_forall_dot_eq_zero H₂ fun z hz => ?_
  by_contra hne
  let u : Vec n₁ := fun a => ∑ b, blockL v a b * z b
  have hu_eq : u = blockL v *ᵥ z := rfl
  have hxzero : H₁ *ᵥ u = 0 := by
    rw [hu_eq, Matrix.mulVec_mulVec, hcomp, ← Matrix.mulVec_mulVec, hz]
    simp
  have hxne : u ≠ 0 := by
    intro hzero
    refine hne ?_
    rw [dotProduct]
    have h1 : u a = 0 := by rw [hzero]; rfl
    exact h1
  have hge : d₁ ≤ hammingNorm u := hd₁ _ hxne hxzero
  have hle : hammingNorm u ≤ hammingNorm v := rowDot_hammingNorm_le v z
  omega
end QECCertificates
