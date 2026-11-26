-- Prove2me | solution 1 for Section5NetFoundation.p792_pack_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:37.820036+00:00
-- url     : https://prove2.me/submissions/396a3fc5-b169-4051-aaf0-983a95752057

import Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet
import Mathlib
set_option autoImplicit false
namespace Section5NetFoundation
end Section5NetFoundation
open Section5NetFoundation
open MeasureTheory Metric in

theorem solution (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (C : Finset (EuclideanSpace ℝ (Fin n)))
    (hC : (↑C : Set (EuclideanSpace ℝ (Fin n))) ⊆ closedBall 0 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε < dist x y) :
    (C.card : ℝ) ≤ (2 / ε + 1) ^ n := by
  have hε2 : 0 < ε / 2 := by positivity
  have hd : Set.PairwiseDisjoint (↑C : Set (EuclideanSpace ℝ (Fin n)))
      (fun c => ball c (ε / 2)) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
  have hsub : (⋃ c ∈ C, ball c (ε / 2)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (1 + ε / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨c, hc, hzc⟩ := hz
    have hc1 : dist c 0 ≤ 1 := hC hc
    rw [mem_ball] at hzc ⊢
    calc dist z 0 ≤ dist z c + dist c 0 := dist_triangle _ _ _
      _ < ε / 2 + 1 := by linarith
      _ = 1 + ε / 2 := by ring
  have h2 := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hsub
  rw [measure_biUnion_finset hd (fun _ _ => measurableSet_ball)] at h2
  rw [Finset.sum_congr rfl (fun c _ => Measure.addHaar_ball_of_pos volume c hε2),
    Finset.sum_const, nsmul_eq_mul,
    Measure.addHaar_ball_of_pos volume (0 : EuclideanSpace ℝ (Fin n)) (by positivity : (0:ℝ) < 1 + ε / 2),
    finrank_euclideanSpace_fin, ← mul_assoc] at h2
  have hV0 : (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ 0 :=
    (measure_ball_pos volume _ one_pos).ne'
  have hVt : (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have h3 := (ENNReal.mul_le_mul_iff_left hV0 hVt).1 h2
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  have heq : 2 / ε + 1 = (1 + ε / 2) / (ε / 2) := by field_simp
  rw [heq, div_pow, le_div_iff₀ (by positivity)]
  exact h4
