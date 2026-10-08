-- Prove2me | solution 1 for VarianceRegularization.FastRates.deviation_event_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:24:09.424233+00:00
-- url     : https://prove2.me/submissions/dfcb548c-1eb2-419c-8f77-456f6f224138

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk
import Definitions.Def_VarianceRegularization_FastRates_Setting

set_option autoImplicit false

open MeasureTheory

namespace D44A60D6

open VarianceRegularization.FastRates VarianceRegularization.Expansion

theorem unif_mem (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (fun _ : Fin n => (1 / (n : ℝ))) ∈ chiSqBall n ρ := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  refine ⟨fun _ => by positivity, ?_, ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hn'
  · have h0 : ∑ _i : Fin n, ((n : ℝ) * (1 / n) - 1) ^ 2 = 0 := by
      rw [mul_one_div_cancel hn', sub_self]; simp
    have h1 : (1 / 2 : ℝ) * ∑ _i : Fin n, ((n : ℝ) * (1 / n) - 1) ^ 2 = 0 := by
      rw [h0, mul_zero]
    exact h1.le.trans hρ

theorem wsum_le (n : ℕ) (hn : 0 < n) (ρ : ℝ) (q : Fin n → ℝ) (hq : q ∈ chiSqBall n ρ)
    (z : Fin n → ℝ) : ∑ i, q i * z i ≤ empMean z + Real.sqrt (2 * ρ / n * empVar z) := by
  obtain ⟨_, hq1, hq2⟩ := hq
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hnpos : (0 : ℝ) < n := by positivity
  obtain ⟨m, hm⟩ : ∃ m, m = empMean z := ⟨_, rfl⟩
  rw [← hm]
  have hsz : ∑ i, z i = n * m := by
    rw [hm, empMean, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
  have hid : (n : ℝ) * (∑ i, q i * z i - m) = ∑ i, ((n : ℝ) * q i - 1) * (z i - m) := by
    have e : ∀ i, ((n : ℝ) * q i - 1) * (z i - m) = n * (q i * z i) - (n * m) * q i - z i + m :=
      fun i => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hq1, hsz]; ring
  have hw : ∑ i, (z i - m) ^ 2 = n * empVar z := by
    have e2 : ∀ i, (z i - m) ^ 2 = z i ^ 2 - (2 * m) * z i + m ^ 2 := fun i => by ring
    simp only [e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsz, empVar, ← hm]; field_simp; ring
  have hu : ∑ i, ((n : ℝ) * q i - 1) ^ 2 ≤ 2 * ρ := by linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => (n : ℝ) * q i - 1)
    (fun i => z i - m)
  have hw0 : 0 ≤ ∑ i, (z i - m) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : ((n : ℝ) * (∑ i, q i * z i - m)) ^ 2 ≤ 2 * ρ * (n * empVar z) := by
    rw [hid, ← hw]; exact hcs.trans (mul_le_mul_of_nonneg_right hu hw0)
  have h3 : (∑ i, q i * z i - m) ^ 2 ≤ 2 * ρ / n * empVar z := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hnpos]
    have : (n : ℝ) * ((∑ i, q i * z i - m) ^ 2 * n) ≤ n * (2 * ρ * empVar z) := by nlinarith [h2]
    exact le_of_mul_le_mul_left this hnpos
  have := Real.abs_le_sqrt h3
  linarith [le_abs_self (∑ i, q i * z i - m)]

theorem bdd (n : ℕ) (hn : 0 < n) (ρ : ℝ) (z : Fin n → ℝ) :
    BddAbove ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' chiSqBall n ρ) :=
  ⟨empMean z + Real.sqrt (2 * ρ / n * empVar z), by
    rintro _ ⟨q, hq, rfl⟩; exact wsum_le n hn ρ q hq z⟩

theorem le_rsup (n : ℕ) (hn : 0 < n) (ρ : ℝ) (q : Fin n → ℝ) (hq : q ∈ chiSqBall n ρ)
    (z : Fin n → ℝ) : ∑ i, q i * z i ≤ robustSup n ρ z :=
  le_csSup (bdd n hn ρ z) ⟨q, hq, rfl⟩

theorem rsup_le (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (z : Fin n → ℝ) (c : ℝ)
    (h : ∀ q ∈ chiSqBall n ρ, ∑ i, q i * z i ≤ c) : robustSup n ρ z ≤ c :=
  csSup_le ⟨_, ⟨_, unif_mem n hn ρ hρ, rfl⟩⟩ (by rintro _ ⟨q, hq, rfl⟩; exact h q hq)

theorem empVar_neg {n : ℕ} (w : Fin n → ℝ) : empVar (fun i => -w i) = empVar w := by
  simp [empVar, empMean, Finset.sum_neg_distrib, neg_sq]

theorem empMean_neg {n : ℕ} (w : Fin n → ℝ) : empMean (fun i => -w i) = -empMean w := by
  simp [empMean, Finset.sum_neg_distrib]

theorem rsup_diff (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (a b : Fin n → ℝ) :
    robustSup n ρ b ≤ robustSup n ρ a - empMean (fun i => a i - b i)
      + Real.sqrt (2 * ρ / n * empVar (fun i => a i - b i)) := by
  apply rsup_le n hn ρ hρ
  intro q hq
  have h1 := le_rsup n hn ρ q hq a
  have h2 : ∑ i, q i * (-(a i - b i)) ≤ -empMean (fun i => a i - b i)
      + Real.sqrt (2 * ρ / n * empVar (fun i => a i - b i)) := by
    have := wsum_le n hn ρ q hq (fun i => -(a i - b i))
    simpa only [empVar_neg, empMean_neg] using this
  have e : ∑ i, q i * b i = ∑ i, q i * a i + ∑ i, q i * (-(a i - b i)) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

theorem rrisk_conv {X : Type*} {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (hconv : ∀ x, ConvexOn ℝ Θ (fun θ => ℓ θ x))
    (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (s : Fin n → X) (p θ : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ Θ) (hθ : θ ∈ Θ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    robustRisk ρ ℓ s (a • p + b • θ) ≤ a * robustRisk ρ ℓ s p + b * robustRisk ρ ℓ s θ := by
  unfold robustRisk
  apply rsup_le n hn ρ hρ
  intro q hq
  have hq0 := hq.1
  calc ∑ i, q i * ℓ (a • p + b • θ) (s i)
      ≤ ∑ i, q i * (a * ℓ p (s i) + b * ℓ θ (s i)) := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_left _ (hq0 i)
        have := (hconv (s i)).2 hp hθ ha hb hab
        simpa [smul_eq_mul] using this
    _ = a * ∑ i, q i * ℓ p (s i) + b * ∑ i, q i * ℓ θ (s i) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        have h1 := le_rsup n hn ρ q hq (fun i => ℓ p (s i))
        have h2 := le_rsup n hn ρ q hq (fun i => ℓ θ (s i))
        exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

theorem risk_conv {X : Type*} [MeasurableSpace X] (P : Measure X) {d : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (hconv : ∀ x, ConvexOn ℝ Θ (fun θ => ℓ θ x))
    (hint : ∀ θ ∈ Θ, Integrable (ℓ θ) P)
    (p θ : EuclideanSpace ℝ (Fin d)) (hp : p ∈ Θ) (hθ : θ ∈ Θ) (a b : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    risk ℓ P (a • p + b • θ) ≤ a * risk ℓ P p + b * risk ℓ P θ := by
  unfold risk
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hint p hp).const_mul a) ((hint θ hθ).const_mul b)]
  apply integral_mono (hint _ (hΘ hp hθ ha hb hab))
    (((hint p hp).const_mul a).add ((hint θ hθ).const_mul b))
  intro x
  have := (hconv x).2 hp hθ ha hb hab
  simpa [smul_eq_mul] using this

theorem risk_lip {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (L : ℝ)
    (hlip : ∀ x, ∀ θ ∈ Θ, ∀ θ' ∈ Θ, |ℓ θ x - ℓ θ' x| ≤ L * ‖θ - θ'‖)
    (hint : ∀ θ ∈ Θ, Integrable (ℓ θ) P) (a b : EuclideanSpace ℝ (Fin d)) (ha : a ∈ Θ)
    (hb : b ∈ Θ) : |risk ℓ P a - risk ℓ P b| ≤ L * ‖a - b‖ := by
  unfold risk
  rw [← integral_sub (hint a ha) (hint b hb)]
  calc |∫ x, ℓ a x - ℓ b x ∂P| ≤ ∫ x, |ℓ a x - ℓ b x| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ _x, L * ‖a - b‖ ∂P :=
        integral_mono ((hint a ha).sub (hint b hb)).abs (integrable_const _)
          (fun x => hlip x a ha b hb)
    _ = L * ‖a - b‖ := by simp

theorem proj_spec {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsClosed K)
    (hne : K.Nonempty) (θ : EuclideanSpace ℝ (Fin d)) :
    proj K θ ∈ K ∧ (∀ z ∈ K, ‖θ - proj K θ‖ ≤ ‖θ - z‖) ∧
      Metric.infDist θ K = ‖θ - proj K θ‖ := by
  obtain ⟨y, hy, hd⟩ := hK.exists_infDist_eq_dist hne θ
  have h : ∃ y ∈ K, ∀ z ∈ K, ‖θ - y‖ ≤ ‖θ - z‖ := ⟨y, hy, fun z hz => by
      rw [← dist_eq_norm, ← dist_eq_norm, ← hd]; exact Metric.infDist_le_dist_of_mem hz⟩
  have hp : proj K θ = h.choose := by unfold proj; rw [dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  rw [hp]
  refine ⟨h1, h2, le_antisymm ?_ ?_⟩
  · rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem h1
  · rw [hd, dist_eq_norm]; exact h2 y hy

theorem nearest_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E)
    (hK : Convex ℝ K) (x y1 y2 : E) (h1 : y1 ∈ K) (h2 : y2 ∈ K)
    (m1 : ∀ z ∈ K, ‖x - y1‖ ≤ ‖x - z‖) (m2 : ∀ z ∈ K, ‖x - y2‖ ≤ ‖x - z‖) : y1 = y2 := by
  have hmid : (1 / 2 : ℝ) • y1 + (1 / 2 : ℝ) • y2 ∈ K :=
    hK h1 h2 (by norm_num) (by norm_num) (by norm_num)
  have e1 := m1 _ hmid
  have heq : ‖x - y1‖ = ‖x - y2‖ := le_antisymm (m1 _ h2) (m2 _ h1)
  have hpar := parallelogram_law_with_norm ℝ (x - y1) (x - y2)
  have ha : (x - y1) + (x - y2) = (2 : ℝ) • (x - ((1 / 2 : ℝ) • y1 + (1 / 2 : ℝ) • y2)) := by
    module
  have hb : (x - y1) - (x - y2) = y2 - y1 := by abel
  rw [ha, hb, norm_smul, Real.norm_two, ← heq] at hpar
  have hN : ‖y2 - y1‖ * ‖y2 - y1‖ ≤ 0 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg _) e1]
  have h0 : ‖y2 - y1‖ = 0 := mul_self_eq_zero.mp (le_antisymm hN (mul_self_nonneg _))
  exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm

theorem S0_convex {X : Type*} [MeasurableSpace X] (P : Measure X) {d : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (hconv : ∀ x, ConvexOn ℝ Θ (fun θ => ℓ θ x))
    (hint : ∀ θ ∈ Θ, Integrable (ℓ θ) P) : Convex ℝ (subOptSet Θ ℓ P 0) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hΘ hx.1 hy.1 ha hb hab, fun θ' hθ' => ?_⟩
  have h1 := risk_conv P Θ hΘ ℓ hconv hint x y hx.1 hy.1 a b ha hb hab
  have h2 := mul_le_mul_of_nonneg_left (hx.2 θ' hθ') ha
  have h3 := mul_le_mul_of_nonneg_left (hy.2 θ' hθ') hb
  have h4 : a * risk ℓ P θ' + b * risk ℓ P θ' = risk ℓ P θ' := by rw [← add_mul, hab, one_mul]
  linarith

theorem empVar_le {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (M : ℝ) (hz : ∀ i, |z i| ≤ M) :
    empVar z ≤ M ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold empVar
  have h1 : ∑ i, z i ^ 2 ≤ ∑ _i : Fin n, M ^ 2 := Finset.sum_le_sum fun i _ => by
    nlinarith [abs_nonneg (z i), sq_abs (z i), hz i]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 : 1 / (n : ℝ) * ∑ i, z i ^ 2 ≤ M ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hnpos]; linarith
  nlinarith [sq_nonneg (empMean z)]

theorem sqrt_bound (L lam γ ρ ε D : ℝ) (n : ℕ) (hn : 0 < n) (hL : 0 ≤ L) (hlam : 0 < lam)
    (hγ : 1 < γ) (hρ : 0 ≤ ρ) (hε : 0 < ε) (hD0 : 0 ≤ D) (hD : lam * D ^ γ ≤ 2 * ε)
    (h27a : (2 * (8 ^ γ * L ^ γ) / lam) ^ (1 / (γ - 1)) * (ρ / n) ^ (γ / (2 * (γ - 1))) ≤ ε) :
    Real.sqrt (2 * ρ / n * (L * D) ^ 2) ≤ ε / 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨a, ha⟩ : ∃ a, a = ρ / (n : ℝ) := ⟨_, rfl⟩
  rw [← ha] at h27a
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg hρ hnpos.le
  have hγ1 : 0 < γ - 1 := by linarith
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * (8 ^ γ * L ^ γ) / lam := ⟨_, rfl⟩
  rw [← hK] at h27a
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hC0 : 0 ≤ a ^ (γ / 2) := Real.rpow_nonneg ha0 _
  have e1 : a ^ (γ / (2 * (γ - 1))) = (a ^ (γ / 2)) ^ (1 / (γ - 1)) := by
    rw [← Real.rpow_mul ha0]; congr 1; field_simp
  rw [e1, ← Real.mul_rpow hK0 hC0] at h27a
  have H1 : K * a ^ (γ / 2) ≤ ε ^ (γ - 1) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg (mul_nonneg hK0 hC0) _) h27a hγ1.le
    rwa [← Real.rpow_mul (mul_nonneg hK0 hC0), one_div_mul_cancel hγ1.ne', Real.rpow_one]
      at this
  have e2 : 2 * Real.sqrt (2 * ρ / n * (L * D) ^ 2) = Real.sqrt 8 * Real.sqrt a * L * D := by
    have : 2 * ρ / n * (L * D) ^ 2 = (2 : ℝ) * a * (L * D) ^ 2 := by rw [ha]; ring
    rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (mul_nonneg hL hD0),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    rw [h8]; ring
  suffices h : (2 * Real.sqrt (2 * ρ / n * (L * D) ^ 2)) ^ γ ≤ ε ^ γ by
    have := (Real.rpow_le_rpow_iff (by positivity) hε.le (by linarith : (0 : ℝ) < γ)).1 h
    linarith
  rw [e2, Real.mul_rpow (by positivity) hD0, Real.mul_rpow (by positivity) hL,
    Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  have es : Real.sqrt a ^ γ = a ^ (γ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ha0]; ring_nf
  rw [es]
  have h8 : Real.sqrt 8 ^ γ ≤ (8 : ℝ) ^ γ := by
    apply Real.rpow_le_rpow (Real.sqrt_nonneg _) _ (by linarith)
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hA0 : 0 ≤ (8 : ℝ) ^ γ := by positivity
  have hB0 : 0 ≤ L ^ γ := Real.rpow_nonneg hL _
  have hE0 : 0 ≤ D ^ γ := Real.rpow_nonneg hD0 _
  have hG : ε ^ γ = ε ^ (γ - 1) * ε := by
    rw [Real.rpow_sub_one hε.ne']; field_simp
  have H1' : 2 * ((8 : ℝ) ^ γ * L ^ γ) * a ^ (γ / 2) ≤ ε ^ (γ - 1) * lam := by
    rw [hK, div_mul_eq_mul_div, div_le_iff₀ hlam] at H1; exact H1
  have H2 := mul_le_mul H1' hD (by positivity) (by positivity)
  have H3 : (8 : ℝ) ^ γ * a ^ (γ / 2) * L ^ γ * D ^ γ ≤ ε ^ γ := by
    rw [hG]
    have h2l : 0 < 2 * lam := by positivity
    have : 2 * lam * ((8 : ℝ) ^ γ * a ^ (γ / 2) * L ^ γ * D ^ γ) ≤
        2 * lam * (ε ^ (γ - 1) * ε) := by nlinarith [H2]
    exact le_of_mul_le_mul_left this h2l
  calc Real.sqrt 8 ^ γ * a ^ (γ / 2) * L ^ γ * D ^ γ
      ≤ (8 : ℝ) ^ γ * a ^ (γ / 2) * L ^ γ * D ^ γ := by gcongr
    _ ≤ ε ^ γ := H3

theorem dist_bound {X : Type*} [MeasurableSpace X] (P : Measure X) {d : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ)
    (hconv : ∀ x, ConvexOn ℝ Θ (fun θ => ℓ θ x))
    (hint : ∀ θ ∈ Θ, Integrable (ℓ θ) P)
    (hS_ne : (subOptSet Θ ℓ P 0).Nonempty) (hS_closed : IsClosed (subOptSet Θ ℓ P 0))
    (lam γ r : ℝ) (hr : 0 < r)
    (hgrowth : ∀ θ ∈ Θ, Metric.infDist θ (subOptSet Θ ℓ P 0) ≤ r →
      ∀ θs ∈ subOptSet Θ ℓ P 0,
        lam * Metric.infDist θ (subOptSet Θ ℓ P 0) ^ γ ≤ risk ℓ P θ - risk ℓ P θs)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ (1 / 2) * lam * r ^ γ)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ subOptSet Θ ℓ P (2 * ε)) :
    lam * ‖θ - proj (subOptSet Θ ℓ P 0) θ‖ ^ γ ≤ 2 * ε := by
  obtain ⟨hpS, _, hinf⟩ := proj_spec (subOptSet Θ ℓ P 0) hS_closed hS_ne θ
  obtain ⟨p, hpdef⟩ : ∃ p, p = proj (subOptSet Θ ℓ P 0) θ := ⟨_, rfl⟩
  rw [← hpdef] at hpS hinf ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = ‖θ - p‖ := ⟨_, rfl⟩
  rw [← hD] at hinf ⊢
  have hpΘ : p ∈ Θ := hpS.1
  have hRθ : risk ℓ P θ ≤ risk ℓ P p + 2 * ε := hθ.2 p hpΘ
  by_cases hDr : D ≤ r
  · have := hgrowth θ hθ.1 (by rw [hinf]; exact hDr) p hpS
    rw [hinf] at this; linarith
  · exfalso
    push_neg at hDr
    have hDpos : 0 < D := hr.trans hDr
    obtain ⟨t, ht⟩ : ∃ t, t = r / D := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have ht1 : t < 1 := by rw [ht, div_lt_one hDpos]; exact hDr
    have htD : t * D = r := by rw [ht]; field_simp
    obtain ⟨c, hc⟩ : ∃ c, c = (1 - t) • p + t • θ := ⟨_, rfl⟩
    have hcΘ : c ∈ Θ := by rw [hc]; exact hΘ hpΘ hθ.1 (by linarith) ht0 (by ring)
    have hcp : c - p = t • (θ - p) := by rw [hc]; module
    have hθc : θ - c = (1 - t) • (θ - p) := by rw [hc]; module
    have hnc : ‖c - p‖ = t * D := by
      rw [hcp, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, hD]
    have hnθc : ‖θ - c‖ = (1 - t) * D := by
      rw [hθc, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), hD]
    have hic : Metric.infDist c (subOptSet Θ ℓ P 0) = r := by
      apply le_antisymm
      · calc Metric.infDist c (subOptSet Θ ℓ P 0) ≤ dist c p :=
              Metric.infDist_le_dist_of_mem hpS
          _ = r := by rw [dist_eq_norm, hnc, htD]
      · have h1 := Metric.infDist_le_infDist_add_dist (x := θ) (y := c)
          (s := subOptSet Θ ℓ P 0)
        rw [hinf, dist_eq_norm, hnθc] at h1
        nlinarith
    have hg := hgrowth c hcΘ hic.le p hpS
    rw [hic] at hg
    have hRc := risk_conv P Θ hΘ ℓ hconv hint p θ hpΘ hθ.1 (1 - t) t (by linarith) ht0
      (by ring)
    rw [← hc] at hRc
    nlinarith [mul_le_mul_of_nonneg_left hRθ ht0, mul_pos (sub_pos.2 ht1) hε]

theorem sqrt_term_le {X : Type*} [MeasurableSpace X] (P : Measure X) {d : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hconv : ∀ x, ConvexOn ℝ Θ (fun θ => ℓ θ x))
    (hlip : ∀ x, ∀ θ ∈ Θ, ∀ θ' ∈ Θ, |ℓ θ x - ℓ θ' x| ≤ L * ‖θ - θ'‖)
    (hint : ∀ θ ∈ Θ, Integrable (ℓ θ) P)
    (hS_ne : (subOptSet Θ ℓ P 0).Nonempty) (hS_closed : IsClosed (subOptSet Θ ℓ P 0))
    (lam γ r : ℝ) (hlam : 0 < lam) (hγ : 1 < γ) (hr : 0 < r)
    (hgrowth : ∀ θ ∈ Θ, Metric.infDist θ (subOptSet Θ ℓ P 0) ≤ r →
      ∀ θs ∈ subOptSet Θ ℓ P 0,
        lam * Metric.infDist θ (subOptSet Θ ℓ P 0) ^ γ ≤ risk ℓ P θ - risk ℓ P θs)
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ (1 / 2) * lam * r ^ γ)
    (h27a : (2 * (8 ^ γ * L ^ γ) / lam) ^ (1 / (γ - 1)) * (ρ / n) ^ (γ / (2 * (γ - 1))) ≤ ε)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ subOptSet Θ ℓ P (2 * ε)) (s : Fin n → X) :
    Real.sqrt (2 * ρ / n *
      empVar (fun i => ℓ θ (s i) - ℓ (proj (subOptSet Θ ℓ P 0) θ) (s i))) ≤ ε / 2 := by
  obtain ⟨hpS, _, _⟩ := proj_spec (subOptSet Θ ℓ P 0) hS_closed hS_ne θ
  have hD := dist_bound P Θ hΘ ℓ hconv hint hS_ne hS_closed lam γ r hr hgrowth ε hε hεr θ hθ
  have hv : empVar (fun i => ℓ θ (s i) - ℓ (proj (subOptSet Θ ℓ P 0) θ) (s i)) ≤
      (L * ‖θ - proj (subOptSet Θ ℓ P 0) θ‖) ^ 2 :=
    empVar_le hn _ _ fun i => hlip (s i) θ hθ.1 _ hpS.1
  have hnn : (0 : ℝ) ≤ 2 * ρ / n := by positivity
  calc _ ≤ Real.sqrt (2 * ρ / n * (L * ‖θ - proj (subOptSet Θ ℓ P 0) θ‖) ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv hnn)
    _ ≤ ε / 2 := sqrt_bound L lam γ ρ ε _ n hn hL hlam hγ hρ hε (norm_nonneg _) hD h27a

theorem event42 {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    {d : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (L : ℝ)
    (hconv : ∀ x, ConvexOn ℝ Θ (fun θ => ℓ θ x))
    (hlip : ∀ x, ∀ θ ∈ Θ, ∀ θ' ∈ Θ, |ℓ θ x - ℓ θ' x| ≤ L * ‖θ - θ'‖)
    (hint : ∀ θ ∈ Θ, Integrable (ℓ θ) P)
    (hS_ne : (subOptSet Θ ℓ P 0).Nonempty) (hS_closed : IsClosed (subOptSet Θ ℓ P 0))
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (ε : ℝ) (hε : 0 < ε) (s : Fin n → X)
    (θ : EuclideanSpace ℝ (Fin d)) (hθE : θ ∈ empSubOptSet Θ ρ ℓ s ε)
    (hθS : θ ∉ subOptSet Θ ℓ P (2 * ε)) :
    ∃ c ∈ subOptSet Θ ℓ P (2 * ε), ε ≤ localizedDeviation Θ ℓ P s c
      + Real.sqrt (2 * ρ / n *
          empVar (fun i => ℓ c (s i) - ℓ (proj (subOptSet Θ ℓ P 0) c) (s i))) := by
  have hS0conv := S0_convex P Θ hΘ ℓ hconv hint
  obtain ⟨hpS, hpmin, _⟩ := proj_spec (subOptSet Θ ℓ P 0) hS_closed hS_ne θ
  obtain ⟨p, hpdef⟩ : ∃ p, p = proj (subOptSet Θ ℓ P 0) θ := ⟨_, rfl⟩
  rw [← hpdef] at hpS hpmin
  have hθΘ : θ ∈ Θ := hθE.1
  have hpΘ : p ∈ Θ := hpS.1
  have hgap : risk ℓ P p + 2 * ε < risk ℓ P θ := by
    by_contra hcon
    push_neg at hcon
    apply hθS
    refine ⟨hθΘ, fun θ' hθ' => ?_⟩
    have := hpS.2 θ' hθ'; linarith
  have hmemΘ : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - t) • p + t • θ ∈ Θ := fun t ht =>
    hΘ hpΘ hθΘ (by linarith [ht.2]) ht.1 (by ring)
  have hcont : ContinuousOn (fun t : ℝ => risk ℓ P ((1 - t) • p + t • θ)) (Set.Icc 0 1) := by
    apply LipschitzOnWith.continuousOn (K := Real.toNNReal (L * ‖θ - p‖))
    apply LipschitzOnWith.of_dist_le'
    intro t ht t' ht'
    rw [Real.dist_eq, Real.dist_eq]
    have := risk_lip P Θ ℓ L hlip hint _ _ (hmemΘ t ht) (hmemΘ t' ht')
    have e : ((1 - t) • p + t • θ) - ((1 - t') • p + t' • θ) = (t - t') • (θ - p) := by module
    rw [e, norm_smul, Real.norm_eq_abs] at this
    calc _ ≤ L * (|t - t'| * ‖θ - p‖) := this
      _ = L * ‖θ - p‖ * |t - t'| := by ring
  have hIVT := intermediate_value_Icc (zero_le_one' ℝ) hcont
  have hmem : risk ℓ P p + 2 * ε ∈ Set.Icc (risk ℓ P ((1 - (0:ℝ)) • p + (0:ℝ) • θ))
      (risk ℓ P ((1 - (1:ℝ)) • p + (1:ℝ) • θ)) := by
    simp only [sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add]
    constructor <;> linarith
  obtain ⟨t, ht, hgt⟩ := hIVT hmem
  obtain ⟨c, hc⟩ : ∃ c, c = (1 - t) • p + t • θ := ⟨_, rfl⟩
  have hcΘ : c ∈ Θ := by rw [hc]; exact hmemΘ t ht
  have hRc : risk ℓ P c = risk ℓ P p + 2 * ε := by rw [hc]; exact hgt
  have hcS : c ∈ subOptSet Θ ℓ P (2 * ε) :=
    ⟨hcΘ, fun θ' hθ' => by have := hpS.2 θ' hθ'; linarith⟩
  have hpc : proj (subOptSet Θ ℓ P 0) c = p := by
    obtain ⟨hqS, hqmin, _⟩ := proj_spec (subOptSet Θ ℓ P 0) hS_closed hS_ne c
    apply nearest_unique _ hS0conv c _ _ hqS hpS hqmin
    intro z hz
    have hcp : c - p = t • (θ - p) := by rw [hc]; module
    have hθc : θ - c = (1 - t) • (θ - p) := by rw [hc]; module
    have h1 : ‖c - p‖ = t * ‖θ - p‖ := by
      rw [hcp, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have h2 : ‖θ - c‖ = (1 - t) * ‖θ - p‖ := by
      rw [hθc, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    have h3 := norm_sub_le_norm_sub_add_norm_sub θ c z
    have h4 := hpmin z hz
    rw [h1]; nlinarith
  refine ⟨c, hcS, ?_⟩
  have hRnθ : robustRisk ρ ℓ s θ ≤ robustRisk ρ ℓ s p + ε := hθE.2 p hpΘ
  have hRnc := rrisk_conv Θ ℓ hconv hn ρ hρ s p θ hpΘ hθΘ (1 - t) t (by linarith [ht.2]) ht.1
    (by ring)
  rw [← hc] at hRnc
  have hdiff := rsup_diff n hn ρ hρ (fun i => ℓ c (s i)) (fun i => ℓ p (s i))
  have hint_eq : ∫ x, (ℓ c x - ℓ p x) ∂P = 2 * ε := by
    rw [integral_sub (hint c hcΘ) (hint p hpΘ)]; unfold risk at hRc; linarith
  unfold localizedDeviation
  rw [hpc, hint_eq]
  unfold robustRisk at hRnθ hRnc
  nlinarith [mul_le_mul_of_nonneg_left hRnθ ht.1, mul_le_mul_of_nonneg_right ht.2 hε.le]

end D44A60D6

open MeasureTheory VarianceRegularization.FastRates in
theorem solution
{X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {d : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ)
    (ℓ : EuclideanSpace ℝ (Fin d) → X → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hconv : ∀ x, ConvexOn ℝ Θ (fun θ => ℓ θ x))
    (hlip : ∀ x, ∀ θ ∈ Θ, ∀ θ' ∈ Θ, |ℓ θ x - ℓ θ' x| ≤ L * ‖θ - θ'‖)
    (hmeas : ∀ θ ∈ Θ, Measurable (ℓ θ)) (hint : ∀ θ ∈ Θ, Integrable (ℓ θ) P)
    (hS_ne : (subOptSet Θ ℓ P 0).Nonempty) (hS_closed : IsClosed (subOptSet Θ ℓ P 0))
    (lam γ r : ℝ) (hlam : 0 < lam) (hγ : 1 < γ) (hr : 0 < r)
    (hgrowth : ∀ θ ∈ Θ, Metric.infDist θ (subOptSet Θ ℓ P 0) ≤ r →
      ∀ θs ∈ subOptSet Θ ℓ P 0,
        lam * Metric.infDist θ (subOptSet Θ ℓ P 0) ^ γ ≤ risk ℓ P θ - risk ℓ P θs)
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ (1 / 2) * lam * r ^ γ)
    (h27a : (2 * (8 ^ γ * L ^ γ) / lam) ^ (1 / (γ - 1)) * (ρ / n) ^ (γ / (2 * (γ - 1))) ≤ ε) :
    (∀ s : Fin n → X,
      (∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε),
        ε - δ ≤ localizedDeviation Θ ℓ P s θ
          + Real.sqrt (2 * ρ / n *
              empVar (fun i => ℓ θ (s i) - ℓ (proj (subOptSet Θ ℓ P 0) θ) (s i)))) →
      ∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε), ε / 2 - δ ≤ localizedDeviation Θ ℓ P s θ) ∧
    Measure.pi (fun _ : Fin n => P) {s | ¬ empSubOptSet Θ ρ ℓ s ε ⊆ subOptSet Θ ℓ P (2 * ε)}
      ≤ Measure.pi (fun _ : Fin n => P)
          {s | ∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε),
            ε / 2 - δ ≤ localizedDeviation Θ ℓ P s θ} := by
  have part1 : ∀ s : Fin n → X,
      (∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε),
        ε - δ ≤ localizedDeviation Θ ℓ P s θ
          + Real.sqrt (2 * ρ / n *
              empVar (fun i => ℓ θ (s i) - ℓ (proj (subOptSet Θ ℓ P 0) θ) (s i)))) →
      ∀ δ > 0, ∃ θ ∈ subOptSet Θ ℓ P (2 * ε), ε / 2 - δ ≤ localizedDeviation Θ ℓ P s θ := by
    intro s h δ hδ
    obtain ⟨θ, hθ, hle⟩ := h δ hδ
    refine ⟨θ, hθ, ?_⟩
    have := D44A60D6.sqrt_term_le P Θ hΘ ℓ L hL hconv hlip hint hS_ne hS_closed lam γ r hlam hγ
      hr hgrowth n hn ρ hρ ε hε hεr h27a θ hθ s
    linarith
  refine ⟨part1, measure_mono ?_⟩
  intro s hs
  simp only [Set.mem_setOf_eq] at hs ⊢
  rw [Set.not_subset] at hs
  obtain ⟨θ, hθE, hθS⟩ := hs
  apply part1 s
  intro δ hδ
  obtain ⟨c, hcS, hc⟩ := D44A60D6.event42 P Θ hΘ ℓ L hconv hlip hint hS_ne hS_closed n hn ρ hρ
    ε hε s θ hθE hθS
  exact ⟨c, hcS, by linarith⟩
