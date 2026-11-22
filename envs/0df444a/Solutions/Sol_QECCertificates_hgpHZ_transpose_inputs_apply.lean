-- Prove2me | solution 1 for QECCertificates.hgpHZ_transpose_inputs_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:56.398419+00:00
-- url     : https://prove2.me/submissions/9d08799e-91b5-4608-ab8d-c313273863b5

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (x : Fin r₁ × Fin n₂)
    (c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂)) :
    hgpHZ H₁.transpose H₂.transpose x c
      = hgpHX H₁ H₂ x (Equiv.sumComm _ _ c) := by
  rcases c with st | ab
  · obtain ⟨s, t⟩ := st; rfl
  · obtain ⟨a, b⟩ := ab; rfl
end QECCertificates
