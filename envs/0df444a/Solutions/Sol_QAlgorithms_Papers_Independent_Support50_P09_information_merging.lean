-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P09.information_merging
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:12:50.03302+00:00
-- url     : https://prove2.me/submissions/7f9c857b-ef3a-4982-9204-3f0533309baa

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

private lemma allParties_cons_x9 {n m : ℕ} (a : Finset (Fin n))
    (x : Fin m → Finset (Fin n)) :
    allParties (Fin.cons a x) = a ∪ allParties x := by
  ext i
  simp [allParties, Fin.exists_fin_succ]

/-- Lemma IV.2, PDF p.14, (36): merge A and B without discarding B.
There may be zero other X registers. -/
theorem solution {n m : ℕ} {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho)
    (a b : Finset (Fin n)) (x : Fin m → Finset (Fin n))
    (hdis : DisjointRegisters (Fin.cons a (Fin.cons b x)) ∅) :
    info .total rho (Fin.cons a (Fin.cons b x)) ∅ - info .total rho ![a,b] ∅ =
      info .total rho (Fin.cons (a ∪ b) x) ∅ := by
  classical
  simp only [info, conditionalMultipartiteInformation, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.union_empty, allParties_cons_x9]
  have ht : allParties (![a,b] : Fin 2 → Finset (Fin n)) = a ∪ b := by
    simp [allParties, Finset.univ_fin2]
  simp only [ht]
  simp only [Finset.union_assoc]
  push_cast
  ring




end
