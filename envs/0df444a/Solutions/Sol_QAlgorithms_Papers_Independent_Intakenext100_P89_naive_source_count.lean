-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P89.naive_source_count
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:36:39.947432+00:00
-- url     : https://prove2.me/submissions/42b71ad8-de00-4e38-a845-04fe7f0b41c9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)
open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

namespace Aux_Q01_naive_source_count
open QAlgorithms.Papers.Independent.Intakenext100.P89

theorem leaf_eq (nGHZ nB k : ℕ) : leafSourceCount nGHZ nB k = 6 * nGHZ * (2 * nB) ^ k := by
  induction k with
  | zero => simp [leafSourceCount]
  | succ n ih =>
    show (2 * nB) * leafSourceCount nGHZ nB n = 6 * nGHZ * (2 * nB) ^ (n + 1)
    rw [ih, pow_succ]
    ring

end Aux_Q01_naive_source_count

open QAlgorithms.Papers.Independent.Intakenext100.P89 in
theorem solution (k nGHZ nB nMeas : ℕ)
    (hGHZ : 0 < nGHZ) (hB : 0 < nB) (hMeas : 0 < nMeas) :
    Fintype.card (NaiveSources k nGHZ nB nMeas) =
      6 * nGHZ * nMeas * (2 * nB) ^ k := by
  simp only [NaiveSources, Fintype.card_prod, Fintype.card_fin]
  rw [Aux_Q01_naive_source_count.leaf_eq]
  ring
