-- Prove2me | solution 1 for OnlineConvexOpt.OnlineBoosting.online_boosting_regret
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:28:39.020386+00:00
-- url     : https://prove2.me/submissions/39f652dc-4545-433a-8077-64ad8fdf2d84

import Mathlib
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_Algorithm
import Definitions.Def_OnlineConvexOpt_OnlineBoosting_WOCL

open OnlineConvexOpt.FirstOrder MeasureTheory

namespace OnlineConvexOpt.OnlineBoosting

noncomputable abbrev bE1 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

lemma bE1_norm : ‖bE1‖ = 1 := by simp [bE1]

lemma bE1_hasGrad (y : EuclideanSpace ℝ (Fin 1)) (C : ℝ) :
    HasGradientAt (fun x : EuclideanSpace ℝ (Fin 1) => inner ℝ bE1 x + C) bE1 y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((innerSL ℝ bE1).hasFDerivAt (x := y)).add_const C
  have heq : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 1)) bE1 = innerSL ℝ bE1 := by
    ext z; simp
  rw [heq]; exact h

lemma bext_eq (x : EuclideanSpace ℝ (Fin 1)) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) (1/2)) :
    Extension (Metric.closedBall 0 1) 1 (1/2) (fun y => inner ℝ bE1 y) x =
      inner ℝ bE1 x + (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1)).toReal⁻¹ *
        ∫ v in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, inner ℝ bE1 ((1/2 : ℝ) • v) := by
  unfold Extension SmoothedFunction
  set B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1
  have hcongr : ∫ v in B, ((fun y => inner ℝ bE1 y + 1 * Metric.infDist y B) (x + (1/2:ℝ) • v)) =
      ∫ v in B, (inner ℝ bE1 x + inner ℝ bE1 ((1/2 : ℝ) • v)) := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro v hv
    have hmem : x + (1/2:ℝ) • v ∈ B := by
      simp only [B, Metric.mem_closedBall, dist_zero_right] at hv ⊢
      simp only [Metric.mem_ball, dist_zero_right] at hx
      calc ‖x + (1/2:ℝ) • v‖ ≤ ‖x‖ + ‖(1/2:ℝ) • v‖ := norm_add_le _ _
        _ ≤ 1 := by rw [norm_smul]; norm_num; linarith
    simp only [Metric.infDist_zero_of_mem hmem, mul_zero, add_zero, inner_add_right]
  rw [hcongr]
  have hvpos : (volume B).toReal ≠ 0 := by
    apply ENNReal.toReal_ne_zero.mpr
    exact ⟨(Metric.measure_closedBall_pos _ _ one_pos).ne', measure_closedBall_lt_top.ne⟩
  have hint : IntegrableOn (fun v : EuclideanSpace ℝ (Fin 1) => inner ℝ bE1 ((1/2 : ℝ) • v)) B := by
    exact ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
      (by fun_prop : Continuous (fun v : EuclideanSpace ℝ (Fin 1) => inner ℝ bE1 ((1/2 : ℝ) • v))).continuousOn
  have hc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 1) => inner ℝ bE1 x) B :=
    integrableOn_const measure_closedBall_lt_top.ne
  rw [integral_add hc hint, setIntegral_const, smul_eq_mul, mul_add, ← mul_assoc,
    show volume.real B = (volume B).toReal from rfl, inv_mul_cancel₀ hvpos, one_mul]

lemma bext_grad : HasGradientAt (Extension (Metric.closedBall 0 1) 1 (1/2)
    (fun y => inner ℝ bE1 y)) bE1 0 := by
  apply (bE1_hasGrad 0 _).congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 1)) (by norm_num : (0:ℝ) < 1/2)]
    with x hx
  exact bext_eq x hx


lemma bE1_hasGrad0 (y : EuclideanSpace ℝ (Fin 1)) :
    HasGradientAt (fun x : EuclideanSpace ℝ (Fin 1) => inner ℝ bE1 x) bE1 y := by
  simpa using bE1_hasGrad y 0

theorem boost_counter : ¬ (∀ {n : ℕ} (d : ℕ) (hd : d = n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (γ : ℝ) (hγpos : 0 < γ) (hγ1 : γ ≤ 1)
    (N T : ℕ) (hN : 0 < N) (hT : 0 < T)
    (δ : ℝ) (hδ : δ = Real.sqrt (D ^ 2 / (γ * N)))
    (η : ℕ → ℝ) (hη : ∀ i : ℕ, 1 ≤ i → η i = min (2 / (i : ℝ)) 1)
    (A : Type) (a : ℕ → A) (H : Set (A → EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hfG : ∀ t, ∀ x, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (W x : ℕ → ℕ → EuclideanSpace ℝ (Fin n))
    (fstage : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (xplay : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : IsOnlineBoostingRun K γ δ G N T η a f W x fstage xplay)
    (RegretBoundW : ℝ)
    (hWOCL : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsGammaWOCL K γ T a H (fun t => W t i) (fun t => fstage t i) RegretBoundW)
    (hstar : A → EuclideanSpace ℝ (Fin n)) (hstar_mem : hstar ∈ convexHull ℝ H)
    (hstar_min : ∀ h ∈ convexHull ℝ H,
      (∑ t ∈ Finset.Icc 1 T, f t (hstar (a t))) ≤ ∑ t ∈ Finset.Icc 1 T, f t (h (a t))),
    (∑ t ∈ Finset.Icc 1 T, f t (xplay t)) - ∑ t ∈ Finset.Icc 1 T, f t (hstar (a t)) ≤
      (5 * d * G * D * T) / (γ * Real.sqrt N) + (2 * G * D / γ) * RegretBoundW) := by
  intro h
  have hδv : (1/2 : ℝ) = Real.sqrt ((2:ℝ) ^ 2 / (1 * ((16:ℕ):ℝ))) := by
    rw [show (2:ℝ) ^ 2 / (1 * ((16:ℕ):ℝ)) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs16 : Real.sqrt ((16:ℕ):ℝ) = 4 := by
    rw [show ((16:ℕ):ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hmemK : ∀ z : EuclideanSpace ℝ (Fin 1), ‖z‖ ≤ 1 → z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    intro z hz; simpa using hz
  have key := @h 1 1 rfl (Metric.closedBall 0 1) (convex_closedBall _ _) ⟨0, by simp⟩
    2 1 (by norm_num) (by norm_num)
    (by
      intro x hx y hy
      simp only [Metric.mem_closedBall, dist_zero_right] at hx hy
      rw [dist_eq_norm]
      calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith)
    1 (by norm_num) le_rfl 16 1 (by norm_num) (by norm_num) (1/2) hδv
    (fun i => min (2 / (i : ℝ)) 1) (fun _ _ => rfl)
    Unit (fun _ => ()) {fun _ => 0} (fun _ y => inner ℝ bE1 y)
    (fun _ => (innerSL ℝ bE1).toLinearMap.convexOn (convex_closedBall _ _))
    (by
      intro t x v hv
      rw [hv.unique (bE1_hasGrad0 x), bE1_norm])
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ y => inner ℝ bE1 y) (fun _ => 0)
    (by
      refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_⟩
      · intro t i _ _ _ _; simp
      · intro t _ _; exact ⟨by simp, fun z _ => by simp⟩
      · intro t i _ _ _ _ v hv
        have := hv.unique bext_grad
        rw [this])
    (-1)
    (by
      intro i _ _ hprem
      exfalso
      have h1 := hprem 1 le_rfl le_rfl bE1 (hmemK _ (by rw [bE1_norm])) (-bE1)
        (hmemK _ (by rw [norm_neg, bE1_norm]))
      simp only [inner_neg_right, real_inner_self_eq_norm_sq, bE1_norm] at h1
      norm_num at h1)
    (fun _ => 0) (subset_convexHull ℝ _ (Set.mem_singleton _))
    (by
      intro g hg
      rw [convexHull_singleton, Set.mem_singleton_iff] at hg
      subst hg; exact le_rfl)
  simp only [Finset.Icc_self, Finset.sum_singleton, sub_self, hs16] at key
  norm_num at key

end OnlineConvexOpt.OnlineBoosting

open OnlineConvexOpt.OnlineBoosting


theorem solution : ¬ (∀ {n : ℕ} (d : ℕ) (hd : d = n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (D G : ℝ) (hDpos : 0 < D) (hGpos : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (γ : ℝ) (hγpos : 0 < γ) (hγ1 : γ ≤ 1)
    (N T : ℕ) (hN : 0 < N) (hT : 0 < T)
    (δ : ℝ) (hδ : δ = Real.sqrt (D ^ 2 / (γ * N)))
    (η : ℕ → ℝ) (hη : ∀ i : ℕ, 1 ≤ i → η i = min (2 / (i : ℝ)) 1)
    (A : Type) (a : ℕ → A) (H : Set (A → EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (hfG : ∀ t, ∀ x, ∀ v, HasGradientAt (f t) v x → ‖v‖ ≤ G)
    (W x : ℕ → ℕ → EuclideanSpace ℝ (Fin n))
    (fstage : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (xplay : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : IsOnlineBoostingRun K γ δ G N T η a f W x fstage xplay)
    (RegretBoundW : ℝ)
    (hWOCL : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      IsGammaWOCL K γ T a H (fun t => W t i) (fun t => fstage t i) RegretBoundW)
    (hstar : A → EuclideanSpace ℝ (Fin n)) (hstar_mem : hstar ∈ convexHull ℝ H)
    (hstar_min : ∀ h ∈ convexHull ℝ H,
      (∑ t ∈ Finset.Icc 1 T, f t (hstar (a t))) ≤ ∑ t ∈ Finset.Icc 1 T, f t (h (a t))),
    (∑ t ∈ Finset.Icc 1 T, f t (xplay t)) - ∑ t ∈ Finset.Icc 1 T, f t (hstar (a t)) ≤
      (5 * d * G * D * T) / (γ * Real.sqrt N) + (2 * G * D / γ) * RegretBoundW) :=
  OnlineConvexOpt.OnlineBoosting.boost_counter
