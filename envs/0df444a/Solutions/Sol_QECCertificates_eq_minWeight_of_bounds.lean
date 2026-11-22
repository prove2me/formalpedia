-- Prove2me | solution 1 for QECCertificates.eq_minWeight_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:33.03653+00:00
-- url     : https://prove2.me/submissions/18a02f59-b0f2-4e00-8ea4-28a3620c1b1a

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Theorems.Thm_QECCertificates_minWeight_le_of_witness
public import Theorems.Thm_QECCertificates_le_minWeight_of_lower

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {d₀ : ℕ}
    (hd : d₀ ≤ n) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace) (hw : hammingNorm E =
      d₀)
    (hlower : ∀ F, F ∈ LinearMap.ker M₁.toLin' → F ∉ M₂.certificateRowSpace → d₀ ≤ hammingNorm F) :
    minWeightKernelOutsideRowSpace M₁ M₂ = d₀ :=
  le_antisymm (minWeight_le_of_witness M₁ M₂ hker hnot hw) (le_minWeight_of_lower M₁ M₂ hd hlower)
end QECCertificates
