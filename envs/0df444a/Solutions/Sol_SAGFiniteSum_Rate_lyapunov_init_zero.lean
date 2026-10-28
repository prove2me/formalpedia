-- Prove2me | solution 1 for SAGFiniteSum.Rate.lyapunov_init_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:47:53.486026+00:00
-- url     : https://prove2.me/submissions/b596577d-6681-40b7-84b7-1c42caea738f

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

open SAGFiniteSum.Rate in
theorem solution {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) (hA : SAGAssumptions f f' L xstar) (hn : 2 ≤ n)
    (x0 : EuclideanSpace ℝ (Fin p)) :
    sagLyap f f' L xstar (zeroTable, x0)
      ≤ SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar + sigmaSq f' xstar / (16 * L)
        + 4 * L / (n : ℝ) * ‖x0 - xstar‖ ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hA.n_pos
  have hL := hA.L_pos
  -- the gradients at the minimizer sum to zero
  have hG : ∑ i, f' i xstar = 0 := by
    have hF : HasFDerivAt (fun x => ∑ i, f i x)
        (∑ i, InnerProductSpace.toDual ℝ _ (f' i xstar)) xstar :=
      HasFDerivAt.fun_sum (fun i _ => hasGradientAt_iff_hasFDerivAt.mp (hA.hasGradient i xstar))
    have hmin : IsLocalMin (fun x => ∑ i, f i x) xstar := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have := hA.minimizer x
      unfold SAGA.Convex.fAvg at this
      have h1 : 0 < 1 / (n : ℝ) := by positivity
      exact le_of_mul_le_mul_left this h1
    have h0 := hmin.hasFDerivAt_eq_zero hF
    rw [← map_sum] at h0
    exact (LinearIsometryEquiv.map_eq_zero_iff _).mp h0
  have hsum0 : ∑ i, ((zeroTable : Fin n → EuclideanSpace ℝ (Fin p)) i - f' i xstar) = 0 := by
    unfold zeroTable
    simp [Finset.sum_neg_distrib, hG]
  have hz : ∑ i, (zeroTable : Fin n → EuclideanSpace ℝ (Fin p)) i = 0 := by
    unfold zeroTable; simp
  have hnorm : ∑ i, ‖(zeroTable : Fin n → EuclideanSpace ℝ (Fin p)) i - f' i xstar‖ ^ 2 =
      ∑ i, ‖f' i xstar‖ ^ 2 := by
    unfold zeroTable; simp
  unfold sagLyap lyap
  simp only []
  rw [hsum0, hz, hnorm, smul_zero, add_zero, norm_zero, inner_zero_left]
  set S := ∑ i, ‖f' i xstar‖ ^ 2 with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hΔ : 0 ≤ SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar := by
    linarith [hA.minimizer x0]
  have ha2 : sagA2 n L * S = sigmaSq f' xstar / (16 * L) - S / (32 * (n : ℝ) ^ 2 * L) := by
    unfold sagA2 sigmaSq
    rw [← hS]
    field_simp
    ring
  have hpos : 0 ≤ S / (32 * (n : ℝ) ^ 2 * L) := by positivity
  have hh : 2 * sagH n * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar) ≤
      SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar := by
    unfold sagH
    have : 0 ≤ 2 / (n : ℝ) * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar) := by
      positivity
    have e : 2 * (1 / 2 - 1 / (n : ℝ)) * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar) =
        (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar) -
          2 / (n : ℝ) * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar) := by ring
    linarith
  have hc : sagC n L = 4 * L / (n : ℝ) := rfl
  rw [hc]
  nlinarith
