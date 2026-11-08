-- Prove2me | solution 1 for SatiationFisherNSW.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:47:36.800641+00:00
-- url     : https://prove2.me/submissions/01fe16fd-defc-4cc7-8e31-c137ea8a3783

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
open scoped Classical

open SatiationFisherNSW in
theorem solution {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hMC : ¬ I.market.IsMoneyClearing) (S : G → Option B) :
    ∏ i, I.val i S = 0 := by
  unfold FisherMarket.IsMoneyClearing at hMC
  push_neg at hMC
  obtain ⟨T, hT⟩ := hMC
  change ∑ j ∈ I.market.N T, (1:ℝ) < ∑ i ∈ T, (1:ℝ) at hT
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_lt] at hT
  by_contra hne
  have hall : ∀ i, I.val i S ≠ 0 := by
    intro i hi
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have key : ∀ i ∈ T, some i ∈ (I.market.N T).image S := by
    intro i hi
    have hex : ∃ j, S j = some i ∧ 0 < I.v i j := by
      by_contra hno
      push_neg at hno
      apply hall i
      unfold NSWInstance.val
      have hs : ∑ j ∈ Finset.univ.filter (fun j => S j = some i), I.v i j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact le_antisymm (hno j (Finset.mem_filter.mp hj).2) (I.v_nonneg i j)
      rw [hs]
      exact min_eq_right (I.c_pos i).le
    obtain ⟨j, hSj, hv⟩ := hex
    refine Finset.mem_image.mpr ⟨j, ?_, hSj⟩
    unfold FisherMarket.N
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, i, hi, ?_⟩
    exact (lt_min hv (I.c_pos i) : 0 < min (I.v i j) (I.c i))
  have hsub : T.image some ⊆ (I.market.N T).image S := by
    intro o ho
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ho
    exact key i hi
  have h1 : (T.image some).card = T.card :=
    Finset.card_image_of_injective _ (Option.some_injective _)
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.card_image_le (s := I.market.N T) (f := S)
  omega
