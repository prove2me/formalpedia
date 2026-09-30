-- Prove2me | solution 1 for SP4RankProfiles.central_five_pairing_channels
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T04:05:01.068057+00:00
-- url     : https://prove2.me/submissions/962b092b-4b27-4ae9-a47e-5d70dd7d5a1a

import Definitions.Def_SP4RankProfiles
import Definitions.Def_SP4RankNine

set_option autoImplicit false

open SP4RankProfiles

theorem solution (g : ℤ) (hg : 0 < g) (M : Fin 8 → ℤ)
    (P : SP4RankNine.CancellationPairing (centralFiveLevel g) M) :
    (∀ i : Fin 8, i.val < 2 →
      P.source i = true ∧ 2 ≤ (P.mate i).val ∧ (P.mate i).val < 6) ∧
    (∀ i : Fin 8, 6 ≤ i.val →
      P.source i = false ∧ 2 ≤ (P.mate i).val ∧ (P.mate i).val < 6) := by
  let C : Finset (Fin 8) := {2, 3, 4, 5}
  let E : Finset (Fin 8) := {0, 1, 6, 7}
  have hC (i : Fin 8) : i ∈ C ↔ 2 ≤ i.val ∧ i.val < 6 := by
    fin_cases i <;> decide
  have hE (i : Fin 8) : i ∈ E ↔ i.val < 2 ∨ 6 ≤ i.val := by
    fin_cases i <;> decide
  have hz (i : Fin 8) (hi : i ∈ C) : centralFiveLevel g i = 0 := by
    fin_cases i <;> simp_all [C, centralFiveLevel]
  have hCE (i : Fin 8) (hi : i ∈ C) : P.mate i ∈ E := by
    by_contra hn
    have hm : P.mate i ∈ C := by
      rw [hE] at hn
      rw [hC]
      omega
    have hz1 := hz i hi
    have hz2 := hz (P.mate i) hm
    cases hs : P.source i
    · have ht : P.source (P.mate i) = true := by simpa [hs] using P.exchange i
      have hl := P.lower (P.mate i) ht
      rw [P.involutive i, hz1, hz2] at hl
      omega
    · have hl := P.lower i hs
      rw [hz1, hz2] at hl
      omega
  have himage : C.image P.mate ⊆ E := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hCE j hj
  have hcard : (C.image P.mate).card = E.card := by
    rw [Finset.card_image_of_injective _ P.mate.injective]
    decide
  have heq : C.image P.mate = E := Finset.eq_of_subset_of_card_le himage hcard.ge
  have hEC (i : Fin 8) (hi : i ∈ E) : P.mate i ∈ C := by
    rw [← heq] at hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have hh := congrArg P.mate hji
    rw [P.involutive j] at hh
    simpa [← hh] using hj
  constructor
  · intro i hi
    have he : i ∈ E := (hE i).mpr (Or.inl hi)
    have hm := (hC (P.mate i)).mp (hEC i he)
    refine ⟨?_, hm⟩
    have htop : centralFiveLevel g i = g := by
      fin_cases i <;> simp_all [centralFiveLevel]
    have htarget := hz (P.mate i) (hEC i he)
    cases hs : P.source i
    · have ht : P.source (P.mate i) = true := by simpa [hs] using P.exchange i
      have hl := P.lower (P.mate i) ht
      rw [P.involutive i, htop, htarget] at hl
      omega
    · rfl
  · intro i hi
    have he : i ∈ E := (hE i).mpr (Or.inr hi)
    have hm := (hC (P.mate i)).mp (hEC i he)
    refine ⟨?_, hm⟩
    have hbottom : centralFiveLevel g i = -g := by
      fin_cases i <;> simp_all [centralFiveLevel]
    have htarget := hz (P.mate i) (hEC i he)
    cases hs : P.source i
    · rfl
    · have hl := P.lower i hs
      rw [hbottom, htarget] at hl
      omega


#print axioms solution
