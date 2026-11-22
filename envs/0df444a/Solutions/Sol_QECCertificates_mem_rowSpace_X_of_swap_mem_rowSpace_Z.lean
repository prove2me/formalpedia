-- Prove2me | solution 1 for QECCertificates.mem_rowSpace_X_of_swap_mem_rowSpace_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:34.490835+00:00
-- url     : https://prove2.me/submissions/0c1ca2a6-46d5-478d-913d-1f7dae62be80

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Theorems.Thm_QECCertificates_swapBlocks_swapBlocks
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_hgpHZ_transpose_inputs_apply
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (h : (fun c => v (swapBlocks c)) ∈ (hgpHZ H₁.transpose H₂.transpose).certificateRowSpace) :
    v ∈ (hgpHX H₁ H₂).certificateRowSpace := by
  have hgen : ∀ x : Fin r₁ × Fin n₂,
      (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) =>
        (hgpHZ H₁.transpose H₂.transpose x) (swapBlocks c)) ∈ (hgpHX H₁ H₂).certificateRowSpace :=
          by
    intro x
    have hrow : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) =>
        (hgpHZ H₁.transpose H₂.transpose x) (swapBlocks c)) = hgpHX H₁ H₂ x := by
      funext c
      rw [hgpHZ_transpose_inputs_apply H₁ H₂ x (swapBlocks c)]
      congr 1
      rcases c with ab | st
      · rfl
      · rfl
    rw [hrow]
    exact Submodule.subset_span ⟨x, rfl⟩
  have hclosure : ∀ w : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) → ZMod 2,
      w ∈ (hgpHZ H₁.transpose H₂.transpose).certificateRowSpace →
      (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => w (swapBlocks c))
        ∈ (hgpHX H₁ H₂).certificateRowSpace := by
    intro w hw
    have hw' : w ∈ Submodule.span (ZMod 2)
        (Set.range fun x : Fin r₁ × Fin n₂ => hgpHZ H₁.transpose H₂.transpose x) := hw
    refine Submodule.span_induction
      (p := fun w _ => (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => w (swapBlocks c))
        ∈ (hgpHX H₁ H₂).certificateRowSpace) ?_ ?_ ?_ ?_ hw'
    · intro g hg
      obtain ⟨x, rfl⟩ := hg
      exact hgen x
    · have hz : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) =>
          (0 : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) → ZMod 2) (swapBlocks c)) = 0 := by
        funext c; rfl
      rw [hz]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      have hadd : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => (a + b) (swapBlocks c))
          = (fun c => a (swapBlocks c)) + fun c => b (swapBlocks c) := by
        funext c; rfl
      rw [hadd]
      exact Submodule.add_mem _ ha hb
    · intro cf a _ ha
      have hsmul : (fun c : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) => (cf • a) (swapBlocks c))
          = cf • (fun c => a (swapBlocks c)) := by
        funext c; rfl
      rw [hsmul]
      exact Submodule.smul_mem _ cf ha
  have := hclosure (fun c => v (swapBlocks c)) h
  simpa only [swapBlocks_swapBlocks] using this
end QECCertificates
