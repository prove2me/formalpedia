-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kOmega_iff_countableCompactHausdorffQuotient
-- status  : ACCEPTED   (prove)
-- author  : @21604
-- created : 2026-11-04T17:48:51.587208+00:00
-- url     : https://prove2.me/submissions/28eba169-9f8e-4a45-88c8-564d781e9e20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u

open CategoryTheory Topology TopologicalSpace
open QAlgorithms.Papers.Independent.Intakethird100.P07

/-- Lemma C.2, PDF p. 38: a space is k-omega iff it is a quotient of a countable coproduct of
compact Hausdorff spaces.

(⟹) The countable covering family `f_i : K_i → X` whose preimages determine the topology is the
same thing as the single map `Σ i, K_i → X` being a quotient map: a set is open in `X` iff all
`f_i`-preimages are open, iff its preimage under `Σ i, K_i → X` is open in the coproduct.

(⟸) Given a quotient map `q : Σ i, K_i → X` with `I` countable, the maps
`q ∘ Sigma.mk i : K_i → X` form a countable covering family (using surjectivity of `q`) and they
determine the topology (using that the coproduct topology is determined by its components). -/
theorem solution (X : Type u) [TopologicalSpace X] :
    IsKOmega X ↔
      ∃ (I : Type u) (_ : Countable I) (K : I → CompHaus.{u})
        (q : (Σ i, K i) → X), IsQuotientMap q := by
  constructor
  · rintro ⟨I, hI, K, f, hcov, htop⟩
    have hco : IsCoinducing (fun s : Σ i, K i => f s.1 s.2) := by
      refine (isCoinducing_iff).2 (fun A => ?_)
      rw [isOpen_sigma_iff]
      exact (htop A).symm
    exact ⟨I, hI, K, (fun s => f s.1 s.2), hco,
      fun x => by
        obtain ⟨i, y, hy⟩ := hcov x
        exact ⟨⟨i, y⟩, hy⟩⟩
  · rintro ⟨I, hI, K, q, hq⟩
    refine ⟨I, hI, K, fun i => ⟨fun y => q ⟨i, y⟩, ?_⟩, ?_, ?_⟩
    · exact hq.continuous.comp (continuous_sigmaMk (i := i))
    · intro x
      obtain ⟨s, hs⟩ := hq.surjective x
      obtain ⟨i, y⟩ := s
      exact ⟨i, y, hs⟩
    · intro A
      have hqA : IsOpen A ↔ IsOpen (q ⁻¹' A) :=
        (isCoinducing_iff.1 hq.isCoinducing A).symm
      have hsig : IsOpen (q ⁻¹' A) ↔ ∀ i, IsOpen ((fun y => q ⟨i, y⟩) ⁻¹' A) := by
        rw [isOpen_sigma_iff]
        exact forall_congr' fun i => Iff.rfl
      exact hqA.trans hsig

end
