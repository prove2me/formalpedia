-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kOmega_countableDisjointUnion
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-04T17:35:50.65128+00:00
-- url     : https://prove2.me/submissions/d5e60a71-a625-4555-afe1-a5284a995ba7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u

open CategoryTheory Topology TopologicalSpace
open QAlgorithms.Papers.Independent.Intakethird100.P07

/-- Lemma C.4: countable disjoint unions preserve k-omega.

Given countable coverings of each X i by compact Hausdorff probes _{i,j}, the family
(i,j) ↦ (x ↦ ⟨i, f_{i,j}(x)⟩) is a countable covering of the sigma type by compact Hausdorff
probes, and it determines the topology: a set A is open in Σ i, X i iff each A_i is open in
X i, iff each probe preimage _{i,j}⁻¹(A_i) is open. -/
theorem solution (I : Type u) [Countable I] (X : I → Type u)
    [∀ i, TopologicalSpace (X i)] (hX : ∀ i, IsKOmega (X i)) :
    IsKOmega (Σ i, X i) := by
  simp only [IsKOmega] at hX
  choose J hJc K f hcov htop using hX
  haveI : ∀ i, Countable (J i) := hJc
  refine ⟨(Σ i, J i), inferInstance, (fun p => K p.1 p.2), ?_, ?_, ?_⟩
  · intro p
    exact ⟨fun x => ⟨p.1, f p.1 p.2 x⟩,
      continuous_sigmaMk.comp (f p.1 p.2).continuous⟩
  · rintro ⟨i, x⟩
    obtain ⟨j, y, hy⟩ := hcov i x
    exact ⟨⟨i, j⟩, y, by
      show (⟨i, (f i j) y⟩ : Sigma X) = ⟨i, x⟩
      rw [hy]⟩
  · intro A
    rw [isOpen_sigma_iff]
    constructor
    · intro hA p
      obtain ⟨i, j⟩ := p
      exact (htop i (Sigma.mk i ⁻¹' A)).1 (hA i) j
    · intro hA i
      refine (htop i (Sigma.mk i ⁻¹' A)).2 (fun j => ?_)
      exact hA ⟨i, j⟩

end
