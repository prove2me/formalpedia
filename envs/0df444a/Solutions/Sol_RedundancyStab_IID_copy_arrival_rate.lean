-- Prove2me | solution 1 for RedundancyStab.IID.copy_arrival_rate
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:08:14.093553+00:00
-- url     : https://prove2.me/submissions/18890c00-0604-4419-ab25-6892700dc05e

import Mathlib
import Definitions.Def_RedundancyStab_IID_Model

open RedundancyStab.IID

theorem solution (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam : ℝ) (s : Fin K) :
    (typesAt K d s).card = (K - 1).choose (d - 1) ∧
      ((typesAt K d s).card : ℝ) * lam / (K.choose d : ℝ) = lam * d / K := by
  classical
  have hcard : (typesAt K d s).card = (K - 1).choose (d - 1) := by
    -- bijection c ↦ c.erase s onto (d-1)-subsets of univ.erase s
    have : (typesAt K d s).card =
        ((Finset.univ.erase s).powersetCard (d - 1)).card := by
      refine Finset.card_bij (fun c _ => c.1.erase s) ?_ ?_ ?_
      · intro c hc
        simp only [typesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩
        rw [Finset.card_erase_of_mem hc, c.2]
      · intro c₁ hc₁ c₂ hc₂ h
        simp only [typesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
        apply Subtype.ext
        have := congrArg (insert s) h
        simpa [Finset.insert_erase hc₁, Finset.insert_erase hc₂] using this
      · intro B hB
        rw [Finset.mem_powersetCard] at hB
        have hsB : s ∉ B := fun h => by simpa using hB.1 h
        refine ⟨⟨insert s B, ?_⟩, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hsB, hB.2]; omega
        · simp [typesAt]
        · simp [Finset.erase_insert hsB]
    rw [this, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  refine ⟨hcard, ?_⟩
  rw [hcard]
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have key := Nat.add_one_mul_choose_eq k j
  have key' : ((k + 1 : ℕ) : ℝ) * (k.choose j : ℝ) = ((k + 1).choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast key
  have hpos : (0 : ℝ) < ((k + 1).choose (j + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hK : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [div_eq_div_iff hpos.ne' hK.ne']
  push_cast at key' ⊢
  linear_combination lam * key'
