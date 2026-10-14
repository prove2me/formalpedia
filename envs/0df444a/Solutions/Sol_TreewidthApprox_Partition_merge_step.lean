-- Prove2me | solution 1 for TreewidthApprox.Partition.merge_step
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:25:33.467261+00:00
-- url     : https://prove2.me/submissions/aed7af7b-b650-472a-b4cb-d9c1720c6323

import Mathlib



theorem solution (m : ℕ) (hm : 4 ≤ m) (b : Fin m → ℕ) (i j : Fin m) (hij : i ≠ j)
    (hmin : ∀ l, l ≠ i → l ≠ j → b i ≤ b l ∧ b j ≤ b l) :
    2 * (b i + b j) ≤ ∑ l, b l := by
  classical
  let R := ((Finset.univ : Finset (Fin m)).erase i).erase j
  have hR : 1 < R.card := by
    simp only [R, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij,Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
    omega
  obtain ⟨k,hk,l,hl,hkl⟩ := Finset.one_lt_card.mp hR
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
  have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
  have hs : b i + b j + b k + b l ≤ ∑ r, b r := by
    have ht := Finset.sum_le_sum_of_subset (f:=b) (Finset.subset_univ ({i,j,k,l} : Finset (Fin m)))
    simpa [Finset.sum_insert, hij, Ne.symm hki, Ne.symm hli,
      Ne.symm hkj, Ne.symm hlj,hkl, add_assoc] using ht
  have hk' := hmin k hki hkj
  have hl' := hmin l hli hlj
  omega
