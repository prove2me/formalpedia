-- Prove2me | solution 1 for QECCertificates.mulVec_mem_spanL_colList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:48:45.416613+00:00
-- url     : https://prove2.me/submissions/e8320598-575e-4f42-954e-1807d415d25d

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_subset_spanL


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (x : Vec k) :
    M *ᵥ x ∈ spanL (colList M) := by
  have hsum : M *ᵥ x = ∑ t : Fin k, x t • (fun i => M i t) := by
    funext i
    rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hsum]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  refine subset_spanL ?_
  rw [colList, matRowList, List.mem_ofFn]
  exact ⟨t, rfl⟩
end QECCertificates
