-- Prove2me | solution 1 for ParallelHAC.Supplement.theorem_9_packing
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:02:45.605988+00:00
-- url     : https://prove2.me/submissions/4ce3e69e-8437-4f1d-9de8-b737f74d2a9b

import Mathlib
namespace ParallelHAC.Supplement

open MeasureTheory Metric

lemma card_bound (k : ℕ) (r R : ℝ) (hr : 0 < r) (hR : 0 ≤ R)
    (P : Set (EuclideanSpace ℝ (Fin k)))
    (hsep : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → r ≤ ‖u - v‖)
    (x : EuclideanSpace ℝ (Fin k)) (hx : P ⊆ Metric.closedBall x R)
    (S : Finset (EuclideanSpace ℝ (Fin k))) (hS : (S : Set _) ⊆ P) :
    (S.card : ℝ) ≤ (1 + 2 * R / r) ^ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : S.card ≤ 1 := Finset.card_le_one.mpr (fun a _ b _ => Subsingleton.elim a b)
    simp only [pow_zero]
    exact_mod_cast this
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  haveI : Nontrivial (EuclideanSpace ℝ (Fin k)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfin]; exact hk)
  set μ : Measure (EuclideanSpace ℝ (Fin k)) := volume
  have hdisj : (S : Set (EuclideanSpace ℝ (Fin k))).PairwiseDisjoint (fun u => ball u (r/2)) := by
    intro u hu v hv huv
    apply Metric.ball_disjoint_ball
    have := hsep u (hS hu) v (hS hv) huv
    rw [dist_eq_norm]; linarith
  have hsub : (⋃ u ∈ S, ball u (r/2)) ⊆ ball x (R + r/2) := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨u, hu, hy⟩ := hy
    have h1 := hx (hS hu)
    rw [mem_closedBall] at h1
    rw [mem_ball] at hy ⊢
    calc dist y x ≤ dist y u + dist u x := dist_triangle _ _ _
      _ < r/2 + R := by linarith
      _ = R + r/2 := by ring
  have hmeas := measure_biUnion_finset (μ := μ) hdisj (fun u _ => measurableSet_ball)
  have hle := measure_mono (μ := μ) hsub
  rw [hmeas] at hle
  have hb : ∀ (y : EuclideanSpace ℝ (Fin k)) (s : ℝ), 0 ≤ s →
      volume (ball y s) = ENNReal.ofReal (s ^ k) * volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) := by
    intro y s hs
    rw [Measure.addHaar_ball volume y hs, hfin]
  simp only [μ] at hle
  rw [Finset.sum_congr rfl (fun u _ => hb u (r/2) (by positivity)), hb x _ (by positivity),
    Finset.sum_const, nsmul_eq_mul] at hle
  have hB0 : volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≠ 0 :=
    (measure_ball_pos _ _ one_pos).ne'
  have hBt : volume (ball (0 : EuclideanSpace ℝ (Fin k)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have h2 := (ENNReal.mul_le_mul_iff_left hB0 hBt).mp hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hpos : (0:ℝ) < (r/2)^k := by positivity
  have : (1 + 2 * R / r) ^ k = (R + r/2)^k / (r/2)^k := by
    rw [← div_pow]; congr 1; field_simp; ring
  rw [this, le_div_iff₀ hpos]
  exact h2

theorem theorem_9_packing (k : ℕ) (r R : ℝ) (hr : 0 < r) (hR : 0 ≤ R)
    (P : Set (EuclideanSpace ℝ (Fin k)))
    (hsep : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → r ≤ ‖u - v‖)
    (x : EuclideanSpace ℝ (Fin k)) (hx : P ⊆ Metric.closedBall x R) :
    P.Finite ∧ (P.ncard : ℝ) ≤ (1 + 3 * R / r) ^ k ∧
      (1 + 3 * R / r) ^ k ≤ (1 + R / r) ^ (3 * k) := by
  have hcb := card_bound k r R hr hR P hsep x hx
  have h23 : (1 + 2 * R / r) ^ k ≤ (1 + 3 * R / r) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    have : 0 ≤ R / r := by positivity
    rw [mul_div_assoc, mul_div_assoc]; linarith
  have hfinite : P.Finite := by
    by_contra hinf
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 + 2 * R / r) ^ k)
    obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
    have := hcb S hS
    rw [hcard] at this
    linarith
  refine ⟨hfinite, ?_, ?_⟩
  · have := hcb hfinite.toFinset (by simp)
    rw [Set.ncard_eq_toFinset_card P hfinite]
    linarith
  · rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    have : 0 ≤ R / r := by positivity
    have e : 3 * R / r = 3 * (R / r) := by ring
    rw [e]; nlinarith [sq_nonneg (R/r), pow_pos (show (0:ℝ) < 1 + R/r by linarith) 3]

end ParallelHAC.Supplement

open ParallelHAC.Supplement in
theorem solution (k : ℕ) (r R : ℝ) (hr : 0 < r) (hR : 0 ≤ R)
    (P : Set (EuclideanSpace ℝ (Fin k)))
    (hsep : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → r ≤ ‖u - v‖)
    (x : EuclideanSpace ℝ (Fin k)) (hx : P ⊆ Metric.closedBall x R) :
    P.Finite ∧ (P.ncard : ℝ) ≤ (1 + 3 * R / r) ^ k ∧
      (1 + 3 * R / r) ^ k ≤ (1 + R / r) ^ (3 * k) :=
  ParallelHAC.Supplement.theorem_9_packing k r R hr hR P hsep x hx
