-- Prove2me | solution 2 for RedundancyStab.IID.copy_arrival_rate
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:56:42.368059+00:00
-- url     : https://prove2.me/submissions/5db1f729-e685-4988-b85a-c81c1d31ba16

import Mathlib
import Definitions.Def_RedundancyStab_IID_Model
set_option autoImplicit false

open RedundancyStab.IID

theorem solution (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam : ℝ) (s : Fin K) :
    (typesAt K d s).card = (K - 1).choose (d - 1) ∧
      ((typesAt K d s).card : ℝ) * lam / (K.choose d : ℝ) = lam * d / K := by
  have hcard : (typesAt K d s).card = (K - 1).choose (d - 1) := by
    have h1 : (typesAt K d s).card = ((Finset.univ.erase s).powersetCard (d - 1)).card := by
      apply Finset.card_bij (fun c _ => c.1.erase s)
      · intro c hc
        simp only [typesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_erase] at hx ⊢
          exact ⟨hx.1, Finset.mem_univ _⟩
        · rw [Finset.card_erase_of_mem hc, c.2]
      · intro c hc c' hc' h
        simp only [typesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
        apply Subtype.ext
        have := congrArg (insert s) h
        simpa [Finset.insert_erase hc, Finset.insert_erase hc'] using this
      · intro t ht
        rw [Finset.mem_powersetCard] at ht
        have hs : s ∉ t := fun h => by simpa using ht.1 h
        refine ⟨⟨insert s t, ?_⟩, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hs, ht.2]; omega
        · simp [typesAt]
        · simp only
          rw [Finset.erase_insert hs]
    rw [h1, Finset.card_powersetCard]
    simp
  refine ⟨hcard, ?_⟩
  rw [hcard]
  have hK : 0 < K := lt_of_lt_of_le hd hdK
  have hK' : (K : ℝ) ≠ 0 := by positivity
  have hch : (K.choose d : ℝ) ≠ 0 := by
    have : 0 < K.choose d := Nat.choose_pos hdK
    positivity
  have key : (K.choose d : ℝ) * d = K * ((K - 1).choose (d - 1) : ℝ) := by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have := Nat.add_one_mul_choose_eq K' d'
    simp only [Nat.add_sub_cancel]
    push_cast
    have h2 : (K' + 1).choose (d' + 1) * (d' + 1) = (K' + 1) * K'.choose d' := this.symm
    exact_mod_cast h2
  field_simp
  linear_combination (-lam) * key
