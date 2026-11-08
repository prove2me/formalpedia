-- Prove2me | solution 1 for SepCostShare.exchange_pi_decrease
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:30:09.659579+00:00
-- url     : https://prove2.me/submissions/ef58db8f-9f20-42fe-96db-87dba0fb368b

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation
import Definitions.Def_SepCostShare_Algorithm

open SepCostShare in
theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E]
    [DecidableEq E] (G : MatroidGame N E) (hG : G.Subadditive) (B : N → Finset E)
    (hB : G.IsProfile B) (i : N) (e f : E) (hi : i ∈ G.users e B)
    (hsel : G.deltaBar B i e < G.d i e ∨ G.deltaBar B i e < G.pi i e)
    (hf : G.IsArgmin B i e f) :
    G.pi i f < G.pi i e ∧ f ∉ B i ∧ G.IsProfile (G.swap B i e f) := by
  classical
  have he : e ∈ B i := (Finset.mem_filter.mp hi).2
  have hfa := hf.1
  have hfbase : (G.M i).IsBase (↑(insert f ((B i).erase e)) : Set E) :=
    (Finset.mem_filter.mp hfa).2
  have hdb : G.deltaBar B i e = G.pi i f := by
    unfold MatroidGame.deltaBar
    rw [dif_pos ⟨f, hfa⟩]
    exact le_antisymm (Finset.inf'_le _ hfa) (Finset.le_inf' _ _ hf.2)
  have hpi : G.pi i f < G.pi i e := by
    rcases hsel with h | h
    · rw [hdb] at h
      have := G.c_nonneg e {i}
      have h' : G.pi i e = G.c e {i} + G.d i e := rfl
      linarith
    · rwa [hdb] at h
  have hfB : f ∉ B i := by
    intro hfB
    have hne : f ≠ e := fun h => by rw [h] at hpi; exact lt_irrefl _ hpi
    have hins : insert f ((B i).erase e) = (B i).erase e :=
      Finset.insert_eq_of_mem (Finset.mem_erase.mpr ⟨hne, hfB⟩)
    rw [hins] at hfbase
    have h1 := hfbase.eq_of_subset_isBase (hB i)
      (Finset.coe_subset.mpr (Finset.erase_subset e (B i)))
    have h2 : (B i).erase e = B i := Finset.coe_injective h1
    have : e ∈ (B i).erase e := by rw [h2]; exact he
    simp at this
  refine ⟨hpi, hfB, ?_⟩
  intro j
  unfold MatroidGame.swap
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact hfbase
  · rw [Function.update_of_ne hj]
    exact hB j
