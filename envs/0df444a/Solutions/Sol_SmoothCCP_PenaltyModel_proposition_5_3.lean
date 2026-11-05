-- Prove2me | solution 1 for SmoothCCP.PenaltyModel.proposition_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:34:49.718644+00:00
-- url     : https://prove2.me/submissions/c65dc650-0248-493d-a9f4-7ae33e15766d

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting
import Theorems.Thm_SmoothCCP_PenaltyModel_proposition_4_1
import Theorems.Thm_SmoothCCP_PenaltyModel_linearization_bound

namespace SCQR

/-- Second-order Taylor bound for a differentiable function with Lipschitz derivative. -/
lemma taylor_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ)
    (hF : Differentiable ℝ F) (K : ℝ)
    (hK : ∀ x y, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ K * ‖x - y‖) (x d : E) :
    |F (x + d) - F x - fderiv ℝ F x d| ≤ |K| * ‖d‖ ^ 2 := by
  have h := (convex_closedBall x ‖d‖).norm_image_sub_le_of_norm_fderiv_le'
    (f := F) (φ := fderiv ℝ F x) (C := |K| * ‖d‖) (x := x) (y := x + d)
    (fun y _ => hF y) (fun y hy => by
      refine (hK y x).trans ?_
      have : ‖y - x‖ ≤ ‖d‖ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hy
      exact (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left this (abs_nonneg K)))
    (Metric.mem_closedBall_self (norm_nonneg d))
    (by simp [Metric.mem_closedBall, dist_eq_norm])
  simp only [add_sub_cancel_left, Real.norm_eq_abs] at h
  calc _ ≤ |K| * ‖d‖ * ‖d‖ := h
    _ = |K| * ‖d‖ ^ 2 := by ring

lemma taylor_grad {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : Differentiable ℝ F) (K : ℝ)
    (hK : ∀ x y, ‖gradient F x - gradient F y‖ ≤ K * ‖x - y‖) (x d : EuclideanSpace ℝ (Fin n)) :
    |F (x + d) - F x - inner ℝ (gradient F x) d| ≤ |K| * ‖d‖ ^ 2 := by
  have hfd : ∀ y, fderiv ℝ F y = InnerProductSpace.toDual ℝ _ (gradient F y) := fun y =>
    (hF y).hasGradientAt.hasFDerivAt.fderiv
  have := taylor_fderiv F hF K (fun x y => by
    rw [hfd, hfd, ← map_sub, LinearIsometryEquiv.norm_map]; exact hK x y) x d
  rwa [hfd, InnerProductSpace.toDual_apply_apply] at this

lemma abs_sup'_sub_le {ι : Type} (s : Finset ι) (hs : s.Nonempty) (a b : ι → ℝ) (B : ℝ)
    (h : ∀ j ∈ s, |a j - b j| ≤ B) : |s.sup' hs a - s.sup' hs b| ≤ B := by
  rw [abs_le]; constructor
  · have : s.sup' hs b ≤ s.sup' hs a + B := Finset.sup'_le _ _ fun j hj =>
      (by linarith [(abs_le.mp (h j hj)).1, Finset.le_sup' a hj] : b j ≤ s.sup' hs a + B)
    linarith
  · have : s.sup' hs a ≤ s.sup' hs b + B := Finset.sup'_le _ _ fun j hj =>
      (by linarith [(abs_le.mp (h j hj)).2, Finset.le_sup' b hj] : a j ≤ s.sup' hs b + B)
    linarith

lemma abs_max0_sub (a b : ℝ) : |max 0 a - max 0 b| ≤ |a - b| := by
  rw [max_comm 0 a, max_comm 0 b]; exact abs_max_sub_max_le_abs a b 0

end SCQR

open SmoothCCP.PenaltyModel in
theorem solution {n m p N : ℕ} {Ξ : Type} (hm : 1 ≤ m) (hN : 1 ≤ N) (ξs : Fin N → Ξ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ)
    (ε α π LH L L' : ℝ) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1)
    (hαN : ∀ k : ℤ, (1 - α) * N ≠ k) (hπ : 0 < π) (hL : 0 < L) (hL' : 0 < L')
    (hf : Differentiable ℝ f)
    (hfL : ∃ Lf : ℝ, ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (hg : ∀ k, Differentiable ℝ (g k))
    (hgL : ∃ Lg : ℝ, ∀ k x y, ‖gradient (g k) x - gradient (g k) y‖ ≤ Lg * ‖x - y‖)
    (hc : ∀ i j, Differentiable ℝ (fun x => c j x (ξs i)))
    (h54 : ∀ (x y : EuclideanSpace ℝ (Fin n)) (i : Fin N) (j : Fin m),
      |c j x (ξs i) - c j y (ξs i)| ≤ L * ‖x - y‖)
    (h55 : ∀ (x y : EuclideanSpace ℝ (Fin n)) (i : Fin N) (j : Fin m),
      ‖gradient (fun z => c j z (ξs i)) x - gradient (fun z => c j z (ξs i)) y‖ ≤ L' * ‖x - y‖) :
    ∃ K : ℝ, ∀ (x d : EuclideanSpace ℝ (Fin n))
        (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      IsSelfAdjoint H → ‖H‖ ≤ LH →
        |penalty hm f g c ξs ε (quarticGamma ε) α π (x + d)
            - model hm f g c ξs ε (quarticGamma ε) α π x H d| ≤ K * ‖d‖ ^ 2 := by
  obtain ⟨Lf, hLf⟩ := hfL
  obtain ⟨Lg, hLg⟩ := hgL
  obtain ⟨hQd, ⟨B, hB⟩, ⟨KQ, hKQ⟩⟩ := proposition_4_1 (N := N) ε α hε hα0 hα1 hN hαN
  set Q := smoothQuantile (N := N) ε (quarticGamma ε) α with hQdef
  refine ⟨|Lf| + |LH| / 2 + π * (p * |Lg| + (|KQ| * L ^ 2 + B * (Real.sqrt N * L'))),
    fun x d H _ hH => ?_⟩
  set z := CN hm c ξs x
  set z' := CN hm c ξs (x + d)
  set y := Ctil hm c ξs x d
  -- f part
  have hfp := SCQR.taylor_grad f hf Lf hLf x d
  -- H part
  have hHp : |1 / 2 * inner ℝ d (H d)| ≤ |LH| / 2 * ‖d‖ ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have h1 := abs_real_inner_le_norm d (H d)
    have h2 := H.le_opNorm d
    have h3 : ‖H‖ ≤ |LH| := hH.trans (le_abs_self _)
    have : ‖d‖ * ‖H d‖ ≤ ‖d‖ * (|LH| * ‖d‖) :=
      mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _)))
        (norm_nonneg _)
    nlinarith
  -- g part
  have hgp : |∑ k, (max 0 (g k (x + d)) - max 0 (g k x + inner ℝ (gradient (g k) x) d))|
      ≤ p * |Lg| * ‖d‖ ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |max 0 (g k (x + d)) - max 0 (g k x + inner ℝ (gradient (g k) x) d)|
        ≤ ∑ _k : Fin p, |Lg| * ‖d‖ ^ 2 := Finset.sum_le_sum fun k _ => by
          refine (SCQR.abs_max0_sub _ _).trans ?_
          have := SCQR.taylor_grad (g k) (hg k) Lg (hLg k) x d
          rwa [show g k (x + d) - (g k x + inner ℝ (gradient (g k) x) d)
            = g k (x + d) - g k x - inner ℝ (gradient (g k) x) d by ring]
      _ = p * |Lg| * ‖d‖ ^ 2 := by simp; ring
  -- Q part
  have hzz : ‖z' - z‖ ≤ L * ‖d‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [Real.norm_eq_abs, Pi.sub_apply]
    apply SCQR.abs_sup'_sub_le
    intro j _
    have := h54 (x + d) x i j
    simpa using this
  have hzy : ‖z' - y‖ ≤ Real.sqrt N * L' * ‖d‖ ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [Real.norm_eq_abs, Pi.sub_apply]
    have hl := linearization_bound hm ξs c L' hL' hc h55 x d
    refine le_trans ?_ hl
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (f := fun i => (z' i - y i) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hQ1 := SCQR.taylor_fderiv Q hQd KQ hKQ z (z' - z)
  rw [add_sub_cancel] at hQ1
  have hQ2 : |fderiv ℝ Q z (z' - y)| ≤ B * (Real.sqrt N * L' * ‖d‖ ^ 2) := by
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ Q z).le_opNorm _).trans ?_
    exact mul_le_mul (hB z) hzy (norm_nonneg _) ((norm_nonneg _).trans (hB z))
  have hQp : |max 0 (Q z') - max 0 (Qtil Q z (y - z))|
      ≤ (|KQ| * L ^ 2 + B * (Real.sqrt N * L')) * ‖d‖ ^ 2 := by
    refine (SCQR.abs_max0_sub _ _).trans ?_
    have e : Q z' - Qtil Q z (y - z)
        = (Q z' - Q z - fderiv ℝ Q z (z' - z)) + fderiv ℝ Q z (z' - y) := by
      simp only [Qtil, map_sub]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have : |KQ| * ‖z' - z‖ ^ 2 ≤ |KQ| * (L * ‖d‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzz 2) (abs_nonneg _)
    nlinarith
  -- assemble
  have e : penalty hm f g c ξs ε (quarticGamma ε) α π (x + d)
      - model hm f g c ξs ε (quarticGamma ε) α π x H d
      = (f (x + d) - f x - inner ℝ (gradient f x) d) - 1 / 2 * inner ℝ d (H d)
        + π * ((∑ k, (max 0 (g k (x + d)) - max 0 (g k x + inner ℝ (gradient (g k) x) d)))
          + (max 0 (Q z') - max 0 (Qtil Q z (y - z)))) := by
    simp only [penalty, model, Finset.sum_sub_distrib]
    ring
  rw [e]
  have hπa : |π| = π := abs_of_pos hπ
  calc _ ≤ |f (x + d) - f x - inner ℝ (gradient f x) d| + |1 / 2 * inner ℝ d (H d)|
        + π * (|∑ k, (max 0 (g k (x + d)) - max 0 (g k x + inner ℝ (gradient (g k) x) d))|
          + |max 0 (Q z') - max 0 (Qtil Q z (y - z))|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, hπa]
        refine add_le_add ((abs_sub _ _).trans le_rfl) ?_
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hπ.le
    _ ≤ |Lf| * ‖d‖ ^ 2 + |LH| / 2 * ‖d‖ ^ 2
        + π * (p * |Lg| * ‖d‖ ^ 2 + (|KQ| * L ^ 2 + B * (Real.sqrt N * L')) * ‖d‖ ^ 2) := by
        gcongr
    _ = _ := by ring
