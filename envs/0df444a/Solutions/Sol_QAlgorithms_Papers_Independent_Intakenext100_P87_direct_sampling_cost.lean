-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P87.direct_sampling_cost
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:24:50.067204+00:00
-- url     : https://prove2.me/submissions/253ff50b-3c23-46ad-9ae0-900bb53b0e5c

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

open QAlgorithms.Papers.Independent.Intakenext100.P87 in
theorem solution (N m : ℕ) (hm : m < N) (bad : Fin N) :
    directMissProbability N m bad = (N - m : ℕ) / (N : ℝ) ∧
    1 / (N : ℝ) ≤ directMissProbability N m bad ∧
    ∀ k : ℝ, 0 ≤ k → directMissProbability N m bad ≤ Real.exp (-k) →
      Real.exp k ≤ (N : ℝ) ∧
      (1 - Real.exp (-k)) * (N : ℝ) ≤ (m : ℝ) := by
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hval : directMissProbability N m bad = (N - m : ℕ) / (N : ℝ) := by
    unfold directMissProbability
    simp only
    have hfil : ((Finset.univ : Finset (Fin N)).powersetCard m).filter (fun S => bad ∉ S) =
        (Finset.univ.erase bad).powersetCard m := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨-, hc⟩, hb⟩
        refine ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => hb (h ▸ hx), Finset.mem_univ _⟩, hc⟩
      · rintro ⟨hs, hc⟩
        exact ⟨⟨Finset.subset_univ _, hc⟩, fun h => (Finset.mem_erase.mp (hs h)).1 rfl⟩
    rw [hfil, Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hid := Nat.choose_mul_succ_eq n m
    have hpos : 0 < (n + 1).choose m := Nat.choose_pos (by omega)
    have hposR : (0 : ℝ) < ((n + 1).choose m : ℝ) := by exact_mod_cast hpos
    simp only [Nat.add_sub_cancel]
    rw [div_eq_div_iff hposR.ne' (by positivity)]
    exact_mod_cast (hid.trans (mul_comm _ _))
  have hcast : ((N - m : ℕ) : ℝ) = (N : ℝ) - m := by rw [Nat.cast_sub hm.le]
  have hmR : (m : ℝ) + 1 ≤ N := by exact_mod_cast hm
  have hlow : 1 / (N : ℝ) ≤ directMissProbability N m bad := by
    rw [hval, hcast]
    exact div_le_div_of_nonneg_right (by linarith) hNR.le
  refine ⟨hval, hlow, fun k hk hle => ⟨?_, ?_⟩⟩
  · have h1 : 1 / (N : ℝ) ≤ Real.exp (-k) := hlow.trans hle
    rw [Real.exp_neg, div_le_iff₀ hNR] at h1
    have hek := Real.exp_pos k
    rw [inv_mul_eq_div, le_div_iff₀ hek, one_mul] at h1
    exact h1
  · rw [hval, hcast, div_le_iff₀ hNR] at hle
    nlinarith
