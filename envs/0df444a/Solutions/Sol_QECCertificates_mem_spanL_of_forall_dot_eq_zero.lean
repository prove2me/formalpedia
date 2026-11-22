-- Prove2me | solution 1 for QECCertificates.mem_spanL_of_forall_dot_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:36.384111+00:00
-- url     : https://prove2.me/submissions/5b87e9ed-6ff0-410e-8c1a-0906af963862

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_exists_ker_dot_ne_zero_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    {y : Vec k} (h : ∀ z : Vec k, M *ᵥ z = 0 → y ⬝ᵥ z = 0) :
    y ∈ spanL (matRowList M) := by
  by_contra hmem
  obtain ⟨z, hz, hdot⟩ := exists_ker_dot_ne_zero_of_not_mem M hmem
  exact hdot (h z hz)
end QECCertificates
