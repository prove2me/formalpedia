-- Prove2me | solution 1 for QECCertificates.le_minWeight_of_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:46:37.61713+00:00
-- url     : https://prove2.me/submissions/8f15d12c-fb6a-46af-9f2d-9d5092aca917

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
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {d₀ : ℕ}
    (hd : d₀ ≤ n)
    (h : ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.certificateRowSpace → d₀ ≤ hammingNorm E) :
    d₀ ≤ minWeightKernelOutsideRowSpace M₁ M₂ := by
  unfold minWeightKernelOutsideRowSpace
  change d₀ ≤ (match Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset) with
    | none => n + 1
    | some a => a)
  split
  · exact Nat.le_trans hd (Nat.le_succ n)
  · rename_i a ha
    have hmem := Finset.mem_of_min ha
    rw [Finset.mem_image] at hmem
    obtain ⟨E, hE, hEw⟩ := hmem
    rw [Set.mem_toFinset] at hE
    rw [← hEw]
    exact h E hE.1 hE.2
end QECCertificates
