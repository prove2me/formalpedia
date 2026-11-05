-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kOmega_quotient
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-04T17:28:50.911303+00:00
-- url     : https://prove2.me/submissions/f3b2ff41-3d4c-4ffc-b4c9-0725ea030c63

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u

open CategoryTheory Topology TopologicalSpace
open QAlgorithms.Papers.Independent.Intakethird100.P07

/-- Lemma C.3, PDF p. 38: every quotient of a k-omega space is k-omega.

If `(K_i → X)_i` is a countable covering family of compact Hausdorff probes determining the
topology of `X`, then composing with the quotient map `q : X → Y` gives a countable family of
probes into `Y`: it still covers (`q` is surjective) and it still determines the topology, because
`A ⊆ Y` is open iff `q ⁻¹' A` is open in `X` (quotient map) iff each `f_i ⁻¹' (q ⁻¹' A)` is open. -/
theorem solution (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    (hX : IsKOmega X) (q : X → Y) (hq : IsQuotientMap q) :
    IsKOmega Y := by
  obtain ⟨I, hI, K, f, hcov, htop⟩ := hX
  refine ⟨I, hI, K, fun i => ⟨q ∘ ⇑(f i), hq.continuous.comp (f i).continuous⟩, ?_, ?_⟩
  · -- the composed probes still cover `Y`
    intro y
    obtain ⟨x, rfl⟩ := hq.surjective y
    obtain ⟨i, y', hy'⟩ := hcov x
    exact ⟨i, y', by rw [← hy']; rfl⟩
  · -- and still determine its topology
    intro A
    have hqA : IsOpen A ↔ IsOpen (q ⁻¹' A) := by
      rw [hq.isCoinducing.eq_coinduced]
      exact isOpen_coinduced
    rw [hqA, htop (q ⁻¹' A)]
    exact Iff.rfl

end
