-- Prove2me | solution 1 for QECCertificates.mem_image_hammingNorm_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:20.144613+00:00
-- url     : https://prove2.me/submissions/d409a103-1698-4c07-8c17-d0a3a8a8f9ed

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness

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
    d₀ ∈ Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset := by
  rw [Finset.mem_image]
  exact ⟨E, by rw [Set.mem_toFinset]; exact ⟨hker, hnot⟩, hw⟩
end QECCertificates
