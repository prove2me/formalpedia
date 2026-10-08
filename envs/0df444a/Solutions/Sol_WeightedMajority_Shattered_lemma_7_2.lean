-- Prove2me | solution 1 for WeightedMajority.Shattered.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:52:42.565113+00:00
-- url     : https://prove2.me/submissions/6faa25e3-8761-45e8-8d89-ce32c439d064

import Mathlib



namespace WeightedMajority.Shattered

theorem pow2_core {ι : Type*} [DecidableEq ι] (e : ι → ℕ) :
    ∀ L : ℕ, ∀ s : Finset ι, (∀ i ∈ s, e i ≤ L) → (2:ℝ)^L ≤ ∑ i ∈ s, (2:ℝ)^(e i) →
      ∃ K ⊆ s, ∑ i ∈ K, (2:ℝ)^(e i) = 2^L := by
  intro L
  induction L with
  | zero =>
    intro s hs hsum
    have h0 : ∀ i ∈ s, e i = 0 := fun i hi => Nat.le_zero.mp (hs i hi)
    by_cases hne : s.Nonempty
    · obtain ⟨i, hi⟩ := hne
      refine ⟨{i}, by simpa using hi, ?_⟩
      simp [h0 i hi]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp at hsum
      norm_num at hsum
  | succ L ih =>
    intro s hs hsum
    by_cases hex : ∃ i ∈ s, e i = L + 1
    · obtain ⟨i, hi, hei⟩ := hex
      refine ⟨{i}, by simpa using hi, ?_⟩
      simp [hei]
    · push_neg at hex
      have hs' : ∀ i ∈ s, e i ≤ L := fun i hi => by
        have := hs i hi; have := hex i hi; omega
      have h1 : (2:ℝ)^L ≤ ∑ i ∈ s, (2:ℝ)^(e i) := by
        have : (2:ℝ)^L ≤ 2^(L+1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      obtain ⟨K1, hK1, hs1⟩ := ih s hs' h1
      have hsplit : ∑ i ∈ s \ K1, (2:ℝ)^(e i) = ∑ i ∈ s, (2:ℝ)^(e i) - 2^L := by
        rw [Finset.sum_sdiff_eq_sub hK1, hs1]
      have h2 : (2:ℝ)^L ≤ ∑ i ∈ s \ K1, (2:ℝ)^(e i) := by
        rw [hsplit]; rw [pow_succ] at hsum; linarith
      obtain ⟨K2, hK2, hs2⟩ := ih (s \ K1) (fun i hi => hs' i (Finset.sdiff_subset hi)) h2
      have hdisj : Disjoint K1 K2 := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have := hK2 hi2
        simp at this
        exact this.2 hi1
      refine ⟨K1 ∪ K2, Finset.union_subset hK1 (hK2.trans Finset.sdiff_subset), ?_⟩
      rw [Finset.sum_union hdisj, hs1, hs2, pow_succ]; ring

theorem l72_core {j : ℕ} (r : Fin j → ℝ) (k : Fin j → ℤ)
    (hr : ∀ i, r i = (2 : ℝ) ^ (k i)) (l : ℤ)
    (hmax : ∀ i, r i ≤ (2 : ℝ) ^ l)
    (hsum : (2 : ℝ) ^ l ≤ ∑ i, r i) :
    ∃ K : Finset (Fin j), ∑ i ∈ K, r i = (2 : ℝ) ^ l := by
  set N : ℤ := ∑ i, |k i| + |l| with hN
  have hN0 : 0 ≤ N := by positivity
  have hki : ∀ i, 0 ≤ k i + N := fun i => by
    have h1 : |k i| ≤ ∑ i, |k i| := Finset.single_le_sum (f := fun i => |k i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have := neg_abs_le (k i)
    have := abs_nonneg l
    linarith
  have hl : 0 ≤ l + N := by have := neg_abs_le l; have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (k i)); linarith
  have hpow : ∀ i, (2:ℝ)^((k i + N).toNat) = r i * 2^N := fun i => by
    rw [hr i, ← zpow_natCast, Int.toNat_of_nonneg (hki i), zpow_add₀ (by norm_num)]
  have hpowL : (2:ℝ)^((l + N).toNat) = 2^l * 2^N := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hl, zpow_add₀ (by norm_num)]
  have hpos : (0:ℝ) < 2^N := by positivity
  obtain ⟨K, -, hK⟩ := pow2_core (fun i => (k i + N).toNat) (l + N).toNat Finset.univ
    (fun i _ => by
      have h := hmax i
      rw [hr i] at h
      have := (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h
      omega)
    (by
      simp only [hpow, hpowL, ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hsum hpos.le)
  refine ⟨K, ?_⟩
  simp only [hpow, hpowL, ← Finset.sum_mul] at hK
  exact mul_right_cancel₀ hpos.ne' hK

end WeightedMajority.Shattered

open WeightedMajority.Shattered


theorem solution {j : ℕ} (r : Fin j → ℝ) (k : Fin j → ℤ)
    (hr : ∀ i, r i = (2 : ℝ) ^ (k i)) (l : ℤ)
    (hmax : ∀ i, r i ≤ (2 : ℝ) ^ l)
    (hsum : (2 : ℝ) ^ l ≤ ∑ i, r i) :
    ∃ K : Finset (Fin j), ∑ i ∈ K, r i = (2 : ℝ) ^ l := by
  exact l72_core r k hr l hmax hsum
