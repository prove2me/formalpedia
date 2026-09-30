-- Prove2me | solution 1 for WangKangXue.SpectralTuran.lemma_2_8
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:56:18.344104+00:00
-- url     : https://prove2.me/submissions/065fb667-27d5-4b89-b338-e85d62b83a23

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
set_option autoImplicit false

theorem solution {α : Type*} [DecidableEq α] (p : ℕ) (hp : 1 ≤ p) (A : Fin p → Finset α) :
    ((Finset.univ.inf' ⟨⟨0, hp⟩, Finset.mem_univ _⟩ A).card : ℤ) ≥
      ∑ i, ((A i).card : ℤ) - ((p : ℤ) - 1) * ((Finset.univ.biUnion A).card : ℤ) := by
  classical
  let U := Finset.univ.biUnion A
  let I := Finset.univ.inf' ⟨⟨0, hp⟩, Finset.mem_univ _⟩ A
  have hAU (i : Fin p) : A i ⊆ U := Finset.subset_biUnion_of_mem A (Finset.mem_univ i)
  have hIA (i : Fin p) : I ⊆ A i := Finset.inf'_le A (Finset.mem_univ i)
  have hIU : I ⊆ U := (hIA ⟨0, hp⟩).trans (hAU ⟨0, hp⟩)
  have hmemI (x : α) : x ∈ I ↔ ∀ i, x ∈ A i := by
    change x ∈ Finset.univ.inf' _ A ↔ _
    erw [Finset.mem_inf']
    simp
  have hcover : U \ I = Finset.univ.biUnion (fun i => U \ A i) := by
    ext x
    simp only [Finset.mem_sdiff, hmemI, Finset.mem_biUnion,
      Finset.mem_univ, true_and, true_implies, not_forall]
    aesop
  have hc : (U \ I).card ≤ ∑ i, (U \ A i).card := by
    rw [hcover]
    exact Finset.card_biUnion_le
  have hcast : ((U \ I).card : ℤ) ≤ ∑ i, ((U \ A i).card : ℤ) := by exact_mod_cast hc
  have hdiff (i : Fin p) : ((U \ A i).card : ℤ) = (U.card : ℤ) - (A i).card := by
    have h := Finset.card_sdiff_add_card_eq_card (hAU i)
    omega
  have hi : ((U \ I).card : ℤ) = (U.card : ℤ) - I.card := by
    have h := Finset.card_sdiff_add_card_eq_card hIU
    omega
  simp_rw [hdiff] at hcast
  rw [Finset.sum_sub_distrib] at hcast
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcast
  rw [hi] at hcast
  change (I.card : ℤ) ≥ ∑ i, ((A i).card : ℤ) - ((p : ℤ) - 1) * (U.card : ℤ)
  nlinarith
