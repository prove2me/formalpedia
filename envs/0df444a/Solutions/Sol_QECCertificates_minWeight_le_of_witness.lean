-- Prove2me | solution 1 for QECCertificates.minWeight_le_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:56.107564+00:00
-- url     : https://prove2.me/submissions/3c5ce0ed-dad1-4c32-8e7d-cc063c1c7020

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Theorems.Thm_QECCertificates_mem_image_hammingNorm_of_witness
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {E : Vec n} {d₀ : ℕ} (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace)
    (hw : hammingNorm E = d₀) :
    minWeightKernelOutsideRowSpace M₁ M₂ ≤ d₀ := by
  have hmem := mem_image_hammingNorm_of_witness M₁ M₂ hker hnot hw
  have hle : Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset)
      ≤ (d₀ : WithTop ℕ) := Finset.min_le hmem
  unfold minWeightKernelOutsideRowSpace
  change (match Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset) with
    | none => n + 1
    | some a => a) ≤ d₀
  split
  · rename_i htop
    have hempty : Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset = ∅ :=
      Finset.min_eq_top.mp
        (show (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset).min = ⊤ from htop)
    rw [hempty] at hmem
    simp at hmem
  · rename_i a ha
    rw [ha] at hle
    exact WithTop.coe_le_coe.mp hle
end QECCertificates
