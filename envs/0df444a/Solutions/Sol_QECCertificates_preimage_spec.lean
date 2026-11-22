-- Prove2me | solution 1 for QECCertificates.preimage_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:33.198994+00:00
-- url     : https://prove2.me/submissions/94e32155-8094-4c55-901a-81f7d774e716

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) {y : Vec m}
    (h : ∃ x : Vec k, M *ᵥ x = y) : M *ᵥ preimage M y = y := by
  rw [preimage, dif_pos h]
  exact Classical.choose_spec h
end QECCertificates
