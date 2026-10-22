-- Prove2me | solution 1 for SymBoolPCSP.LPRounding.case1_claim
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:19:08.018835+00:00
-- url     : https://prove2.me/submissions/90f2e3ab-5f64-4f5c-861d-1101645a8a6a

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_LPRounding_Basic

set_option autoImplicit false

/-- affine functional avoiding lemma -/
lemma exists_avoid {n : ℕ} {ι : Type*} (I : Finset ι) (r : ι → Fin n → ℚ) (c : ι → ℚ)
    (K : Set (Fin n → ℚ)) (hK : Convex ℚ K) (hne : K.Nonempty)
    (hw : ∀ i ∈ I, ∃ w ∈ K, ∑ j, r i j * w j - c i ≠ 0) :
    ∃ v ∈ K, ∀ i ∈ I, ∑ j, r i j * v j - c i ≠ 0 := by
  classical
  induction I using Finset.induction_on with
  | empty => obtain ⟨v, hv⟩ := hne; exact ⟨v, hv, by simp⟩
  | insert a I ha ih =>
    obtain ⟨v, hvK, hv⟩ := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
    by_cases hva : ∑ j, r a j * v j - c a ≠ 0
    · refine ⟨v, hvK, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hva
      · exact hv i hi
    · simp only [not_not] at hva
      obtain ⟨w, hwK, hwa⟩ := hw a (Finset.mem_insert_self a I)
      -- bad parameters
      let bad : Finset ℚ := I.image (fun i =>
        (∑ j, r i j * v j - c i) / ((∑ j, r i j * v j - c i) - (∑ j, r i j * w j - c i)))
      obtain ⟨s, hs0, hs1, hsb⟩ : ∃ s : ℚ, 0 < s ∧ s ≤ 1 ∧ s ∉ bad := by
        have hinf : (Set.Ioc (0 : ℚ) 1).Infinite := Set.Ioc_infinite (by norm_num)
        obtain ⟨s, hs, hsb⟩ := hinf.exists_notMem_finset bad
        exact ⟨s, hs.1, hs.2, hsb⟩
      have hsK : (1 - s) • v + s • w ∈ K := hK hvK hwK (by linarith) hs0.le (by ring)
      refine ⟨(1 - s) • v + s • w, hsK, fun i hi => ?_⟩
      have key : ∀ i, ∑ j, r i j * ((1 - s) • v + s • w) j - c i =
          (1 - s) * (∑ j, r i j * v j - c i) + s * (∑ j, r i j * w j - c i) := by
        intro i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have : ∑ j, r i j * ((1 - s) * v j + s * w j) =
            (1 - s) * ∑ j, r i j * v j + s * ∑ j, r i j * w j := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [this]; ring
      rw [key]
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rw [hva]; simpa using ⟨hs0.ne', hwa⟩
      · intro h0
        apply hsb
        rw [Finset.mem_image]
        refine ⟨i, hi, ?_⟩
        have hvi := hv i hi
        have hd : (∑ j, r i j * v j - c i) - (∑ j, r i j * w j - c i) ≠ 0 := by
          intro hd
          apply hvi
          have : (1 - s) * (∑ j, r i j * v j - c i) + s * (∑ j, r i j * w j - c i) =
            (∑ j, r i j * v j - c i) := by linear_combination (-s) * hd
          rw [this] at h0; exact h0
        rw [div_eq_iff hd]
        linear_combination h0

lemma avoid_simplex (n : ℕ) (hn : 0 < n) (M : Fin n → Fin n → ℚ) (I : Finset (Fin n))
    (c : Fin n → ℚ) (hI : ∀ i ∈ I, M i i ≠ c i) :
    ∃ v : Fin n → ℚ, (∀ j, 0 ≤ v j ∧ v j ≤ 1) ∧ ∑ j, v j = 1 ∧
      ∀ i ∈ I, ∑ j, M i j * v j ≠ c i := by
  have hK : Convex ℚ {v : Fin n → ℚ | (∀ j, 0 ≤ v j ∧ v j ≤ 1) ∧ ∑ j, v j = 1} := by
    intro v hv w hw a b ha hb hab
    refine ⟨fun j => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hv.1 j; have := hw.1 j
      constructor <;> nlinarith [hv.1 j, hw.1 j]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hv.2, hw.2]
      linarith
  have hne : ({v : Fin n → ℚ | (∀ j, 0 ≤ v j ∧ v j ≤ 1) ∧ ∑ j, v j = 1}).Nonempty := by
    refine ⟨Pi.single ⟨0, hn⟩ 1, fun j => ?_, by simp⟩
    by_cases h : j = ⟨0, hn⟩ <;> simp [h]
  obtain ⟨v, hv, hv2⟩ := exists_avoid I M c _ hK hne (fun i hi => by
    refine ⟨Pi.single i 1, ⟨fun j => ?_, by simp⟩, ?_⟩
    · by_cases h : j = i <;> simp [h]
    · simpa [Pi.single_apply] using sub_ne_zero.mpr (hI i hi))
  exact ⟨v, hv.1, hv.2, fun i hi => sub_ne_zero.mp (hv2 i hi)⟩

theorem solution (n : ℕ) (hn : 0 < n) (M : Fin n → Fin n → ℚ)
    (hM : ∀ i j, 0 ≤ M i j ∧ M i j ≤ 1) (hdiag : ∀ i, M i i = 0 ∨ M i i = 1) :
    ∃ v : Fin n → ℚ, (∀ j, 0 ≤ v j ∧ v j ≤ 1) ∧ ∑ j, v j = 1 ∧
      ∀ i, ∑ j, M i j * v j ≠ 1 / 2 := by
  obtain ⟨v, h1, h2, h3⟩ := avoid_simplex n hn M Finset.univ (fun _ => 1 / 2) (fun i _ => by
    rcases hdiag i with h | h <;> rw [h] <;> norm_num)
  exact ⟨v, h1, h2, fun i => h3 i (Finset.mem_univ i)⟩
