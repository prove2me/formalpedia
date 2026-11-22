-- Prove2me | solution 1 for QECCertificates.mem_rowSpace_hgpHZ_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:16.617933+00:00
-- url     : https://prove2.me/submissions/f52ce9cb-40d9-434f-b0dc-35ba6bb733e5

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_sum_smul_hgpHZ_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    {C : Matrix (Fin n₁) (Fin r₂) (ZMod 2)}
    (hU : blockL v = C * H₂) (hR : blockR v = H₁ * C) :
    v ∈ (hgpHZ H₁ H₂).certificateRowSpace := by
  have hv : v = ∑ p : Fin n₁ × Fin r₂, C p.1 p.2 • hgpHZ H₁ H₂ p := by
    funext c
    rw [sum_smul_hgpHZ_apply]
    rcases c with ab | st
    · obtain ⟨a, b⟩ := ab
      rw [← hU]
      rfl
    · obtain ⟨s, t⟩ := st
      rw [← hR]
      rfl
  rw [hv]
  refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨p, rfl⟩
end QECCertificates
