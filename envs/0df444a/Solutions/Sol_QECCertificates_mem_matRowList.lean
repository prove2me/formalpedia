-- Prove2me | solution 1 for QECCertificates.mem_matRowList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:55.276082+00:00
-- url     : https://prove2.me/submissions/09eb1a04-63cb-49d2-8a3b-74417dc85e01

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
theorem _root_.solution {m k : ℕ} {M : Matrix (Fin m) (Fin k) (ZMod 2)} {y : Vec k} :
    y ∈ matRowList M ↔ ∃ i, (fun j => M i j) = y := by
  rw [matRowList, List.mem_ofFn]
end QECCertificates
