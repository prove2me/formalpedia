-- Prove2me | solution 1 for QECCertificates.swapBlocks_swapBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:43:30.993624+00:00
-- url     : https://prove2.me/submissions/2587d3c0-2be1-4a2b-90d2-dcc59fd8556f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {α β : Type*} (c : α ⊕ β) : swapBlocks (swapBlocks c) = c := by
  rcases c with ab | st <;> rfl
end QECCertificates
