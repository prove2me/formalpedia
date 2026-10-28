-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.noCooccurrence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:12:25.790132+00:00
-- url     : https://prove2.me/submissions/c9b1005d-4f96-4820-bfee-d5ea4bcca46d

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

section Compression

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)] [hD : ∀ i, Nonempty (D i)]

variable {R : Type} [Fintype R] [hR : Nonempty R]

variable (phi : EuclideanSpace ℂ (RegisterBasis D × R)) (hphi : ‖phi‖ = 1)

include hphi hD hR

/-- Lemma III.6, PDF p.11: "pair" means DISTINCT elements, as its
column-dependence proof requires. Unique solvability includes existence. -/
theorem solution (hm : 0 < m) (L : Fin m → Finset (Fin m))
    (hunique : ∃! Q : Fin m → ℝ,
      ∀ j, (∑ i ∈ L j, Q i) = entropyThreshold (pureDensity phi) (L j)) :
    ¬ ∃ j k : Fin m, j ≠ k ∧ ∀ i, (j ∈ L i ↔ k ∈ L i) := by
  classical
  rintro ⟨j, k, hjk, hcols⟩
  obtain ⟨Q, hQ, hu⟩ := hunique
  let Q' : Fin m → ℝ := fun i => Q i + (if i = j then 1 else 0) -
    (if i = k then 1 else 0)
  have hQ' : ∀ a, (∑ i ∈ L a, Q' i) =
      entropyThreshold (pureDensity phi) (L a) := by
    intro a
    dsimp [Q']
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hQ]
    simp only [Finset.sum_ite_eq']
    by_cases hj : j ∈ L a
    · simp [hj, (hcols a).mp hj]
    · have hk : k ∉ L a := fun hk => hj ((hcols a).mpr hk)
      simp [hj, hk]
  have heq := congrFun (hu Q' hQ') j
  have hkj : j ≠ k := hjk
  simp [Q', hkj] at heq


end Compression



end
