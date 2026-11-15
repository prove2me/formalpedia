-- Prove2me | solution 1 for PagingDelay.PMD.lemma_34
-- status  : ACCEPTED   (prove)
-- author  : @licsth
-- created : 2026-11-14T08:45:43.20907+00:00
-- url     : https://prove2.me/submissions/170e0fed-71c4-4f43-8121-673d7b89f6df

import Definitions.Def_PagingDelay_PMD_Path

/-!
Lemma 34 (properties of the rounding map), adapted from `lem:map` of the authors'
formalization (`PagingWithDelay/Rounding/Map.lean`, `zmap`).
-/

namespace PagingDelay.PMD.Lemma34

open PagingDelay.PMD

/-- With `δ = 1/(2k+1)` and `k ≥ 1`: `0 < δ`, `1 - δ ≥ 2/3` and `k = (k + 1/2)(1 - δ)`. -/
lemma delta_facts {k : ℕ} (hk : 1 ≤ k) :
    0 < delta k ∧ 2 / 3 ≤ 1 - delta k ∧ (k : ℝ) = (k + 1 / 2) * (1 - delta k) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < 2 * k + 1 := by linarith
  unfold delta
  refine ⟨by positivity, ?_, ?_⟩
  · rw [le_sub_iff_add_le, div_add_div _ _ (by norm_num) hpos.ne', div_le_one (by positivity)]
    nlinarith
  · field_simp
    ring

lemma roundingMap_apply (k : ℕ) (u : ℝ) :
    roundingMap k u = max 0 (2 * ((1 - u) / (1 - delta k)) - 1) := rfl

/-- The map is nonincreasing and `3`-Lipschitz: `(z(u') - z(u))⁺ ≤ 3 (u - u')⁺`. -/
lemma roundingMap_sub_le {k : ℕ} (hk : 1 ≤ k) (u u' : ℝ) :
    max 0 (roundingMap k u' - roundingMap k u) ≤ 3 * max 0 (u - u') := by
  obtain ⟨-, hδ1, -⟩ := delta_facts hk
  have hc : 0 < 1 - delta k := by linarith
  set a := 2 * ((1 - u) / (1 - delta k)) - 1
  set a' := 2 * ((1 - u') / (1 - delta k)) - 1
  have e : a' - a = 2 * (u - u') / (1 - delta k) := by
    simp only [a, a']
    field_simp
    ring
  have hle : max 0 a' - max 0 a ≤ max 0 (a' - a) := by
    simpa using max_sub_max_le_max 0 a' 0 a
  have hd : max 0 (a' - a) ≤ 3 * max 0 (u - u') := by
    apply max_le (by positivity)
    rw [e, div_le_iff₀ hc]
    rcases le_total 0 (u - u') with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  exact max_le (by positivity) (hle.trans hd)

lemma roundingMap_lipschitz {k : ℕ} (hk : 1 ≤ k) : LipschitzWith 3 (roundingMap k) := by
  refine LipschitzWith.of_dist_le_mul fun u u' => ?_
  rw [Real.dist_eq, Real.dist_eq, abs_le]
  have h1 := roundingMap_sub_le hk u u'
  have h2 := roundingMap_sub_le hk u' u
  have h3 : max 0 (u - u') ≤ |u - u'| := max_le (abs_nonneg _) (le_abs_self _)
  have h4 : max 0 (u' - u) ≤ |u - u'| := max_le (abs_nonneg _) (by rw [abs_sub_comm]; exact le_abs_self _)
  push_cast
  constructor
  · linarith [le_max_right 0 (roundingMap k u' - roundingMap k u)]
  · linarith [le_max_right 0 (roundingMap k u - roundingMap k u')]

lemma roundingMap_antitone {k : ℕ} (hk : 1 ≤ k) : Antitone (roundingMap k) := by
  intro u u' huu'
  have h := roundingMap_sub_le hk u u'
  rw [max_eq_left (by linarith : u - u' ≤ 0), mul_zero] at h
  linarith [le_max_right 0 (roundingMap k u' - roundingMap k u)]

theorem main (n k : ℕ) (hk : 1 ≤ k) (x : Fin n → ℝ)
    (hx : ∀ i, delta k ≤ x i ∧ x i ≤ 1)
    (hmass : (n : ℝ) - k ≤ ∑ i, x i) :
    (∀ i, 0 ≤ roundingMap k (x i) ∧ roundingMap k (x i) ≤ 1) ∧
    (∀ i, x i = delta k → roundingMap k (x i) = 1) ∧
    (∑ i, roundingMap k (x i)) ≤ (k : ℝ) ∧
    AntitoneOn (roundingMap k) (Set.Icc (delta k) 1) ∧
    LipschitzOnWith 3 (roundingMap k) (Set.Icc (delta k) 1) := by
  obtain ⟨hδ0, hδ1, hkδ⟩ := delta_facts hk
  have hc : 0 < 1 - delta k := by linarith
  set u : Fin n → ℝ := fun i => (1 - x i) / (1 - delta k) with hu
  have hu0 : ∀ i, 0 ≤ u i := fun i => div_nonneg (by linarith [(hx i).2]) hc.le
  have hu1 : ∀ i, u i ≤ 1 := fun i => (div_le_one hc).2 (by linarith [(hx i).1])
  have hz : ∀ i, roundingMap k (x i) = max 0 (2 * u i - 1) := fun i => rfl
  refine ⟨fun i => ⟨by rw [hz]; exact le_max_left _ _, by
    rw [hz]; exact max_le (by norm_num) (by linarith [hu1 i])⟩, ?_, ?_,
    (roundingMap_antitone hk).antitoneOn _, (roundingMap_lipschitz hk).lipschitzOnWith⟩
  · intro i hi
    rw [roundingMap_apply, hi, div_self (by linarith)]
    norm_num
  -- `∑ u ≤ k + 1/2`
  have hsumu : ∑ i, u i ≤ k + 1 / 2 := by
    have : ∑ i, u i = (n - ∑ i, x i) / (1 - delta k) := by
      simp only [hu, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [this, div_le_iff₀ hc]
    linarith
  -- only the pages in `A = {i | uᵢ > 1/2}` contribute
  set A := Finset.univ.filter (fun i => 1 / 2 < u i) with hA
  have hsumA : ∑ i, roundingMap k (x i) = ∑ i ∈ A, (2 * u i - 1) := by
    rw [hA, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz]
    split_ifs with h
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  have h1 : ∑ i ∈ A, (2 * u i - 1) ≤ A.card := by
    rw [← mul_one (A.card : ℝ), ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ => by linarith [hu1 i]
  have h2 : ∑ i ∈ A, (2 * u i - 1) ≤ 2 * (k + 1 / 2) - A.card := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : ∑ i ∈ A, u i ≤ ∑ i, u i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hu0 i
    linarith
  rw [hsumA]
  rcases le_or_gt A.card k with h | h
  · exact h1.trans (by exact_mod_cast h)
  · have : (k : ℝ) + 1 ≤ A.card := by exact_mod_cast h
    linarith

end PagingDelay.PMD.Lemma34

open PagingDelay.PMD in
theorem solution (n k : ℕ) (hk : 1 ≤ k) (x : Fin n → ℝ)
    (hx : ∀ i, delta k ≤ x i ∧ x i ≤ 1)
    (hmass : (n : ℝ) - k ≤ ∑ i, x i) :
    (∀ i, 0 ≤ roundingMap k (x i) ∧ roundingMap k (x i) ≤ 1) ∧
    (∀ i, x i = delta k → roundingMap k (x i) = 1) ∧
    (∑ i, roundingMap k (x i)) ≤ (k : ℝ) ∧
    AntitoneOn (roundingMap k) (Set.Icc (delta k) 1) ∧
    LipschitzOnWith 3 (roundingMap k) (Set.Icc (delta k) 1) :=
  PagingDelay.PMD.Lemma34.main n k hk x hx hmass
