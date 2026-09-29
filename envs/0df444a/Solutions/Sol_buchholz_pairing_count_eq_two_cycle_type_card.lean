-- Prove2me | solution 1 for buchholz_pairing_count_eq_two_cycle_type_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T03:42:12.76164+00:00
-- url     : https://prove2.me/submissions/7072966e-954b-4e4a-a88d-fc3a9adb3341

import Theorems.Thm_buchholz_pairing_equiv_two_cycle_type

open MatrixCompletion

/-- Source: Candes--Recht, Section 6.1, Lemma 6.1, PDF p. 25.  This is the
formal cardinality bridge from the equivalence between pair partitions and
cycle type `2^n` to equality of their finite cardinalities. -/
theorem solution (n : Nat) :
    Fintype.card (BuchholzPairing n) =
      ({g | g.cycleType = Multiset.replicate n 2} :
        Finset (Equiv.Perm (Fin (2 * n)))).card := by
  classical
  let e := Classical.choice (buchholz_pairing_equiv_two_cycle_type n)
  have h :=
    Fintype.card_congr e
  rw [h]
  rw [Fintype.card_subtype]
