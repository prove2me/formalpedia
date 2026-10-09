-- Prove2me | solution 1 for VarianceRegularization.FastRates.fast_rate_theorem5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T17:56:20.145474+00:00
-- url     : https://prove2.me/submissions/893101d0-4447-4497-9308-81bbf2e59bed

import Mathlib
import Definitions.Def_VarianceRegularization_FastRates_RobustRisk
import Definitions.Def_VarianceRegularization_FastRates_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

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
theorem d44_dev
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


namespace P82cd

lemma int_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma abs_integral_le_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : |∫ x, F x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := C)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  simpa [Real.norm_eq_abs] using this

/-- Hoeffding step: a measurable function with oscillation at most `c`. -/
lemma hoeff_step {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (G : Ω → ℝ) (hG : Measurable G) (c B : ℝ) (hc : 0 ≤ c) (hB : ∀ z, |G z| ≤ B)
    (hosc : ∀ z z', G z' - G z ≤ c) (t : ℝ) :
    ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 8 * t ^ 2) := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  have hbdd : BddBelow (Set.range G) := ⟨-B, by
    rintro _ ⟨z, rfl⟩; have := hB z; rw [abs_le] at this; linarith⟩
  set A := ⨅ z, G z with hA
  have hmem : ∀ z, G z ∈ Set.Icc A (A + c) := by
    intro z
    refine ⟨ciInf_le hbdd z, ?_⟩
    have : G z - c ≤ A := le_ciInf fun z' => by have := hosc z' z; linarith
    linarith
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := G) (a := A) (b := A + c)
    hG.aemeasurable (Filter.Eventually.of_forall hmem)
  have h1 := hs.mgf_le t
  have hcoe : (((‖(A + c) - A‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 / 4 := by
    have : (A + c) - A = c := by ring
    rw [this]
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  rw [hcoe] at h1
  unfold mgf at h1
  calc ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 4 * t ^ 2 / 2) := h1
    _ = Real.exp (c ^ 2 / 8 * t ^ 2) := by ring_nf


end P82cd

namespace F198

open P82cd

lemma bdd_of_abs {T : Type*} (f : T → ℝ) (B : ℝ) (hf : ∀ τ, |f τ| ≤ B) :
    BddAbove (Set.range f) :=
  ⟨B, by rintro _ ⟨τ, rfl⟩; exact (le_abs_self _).trans (hf τ)⟩

lemma abs_iSup_le {T : Type*} [Nonempty T] (f : T → ℝ) (B : ℝ) (hf : ∀ τ, |f τ| ≤ B) :
    |⨆ τ, f τ| ≤ B := by
  obtain ⟨τ0⟩ := ‹Nonempty T›
  rw [abs_le]; constructor
  · have h1 := le_ciSup (bdd_of_abs f B hf) τ0
    have h2 := (abs_le.mp (hf τ0)).1
    linarith
  · exact ciSup_le fun τ => (le_abs_self _).trans (hf τ)

lemma iSup_le_iSup_add {T : Type*} [Nonempty T] (f g : T → ℝ) (B c : ℝ)
    (hg : ∀ τ, |g τ| ≤ B) (hfg : ∀ τ, f τ ≤ g τ + c) : ⨆ τ, f τ ≤ (⨆ τ, g τ) + c :=
  ciSup_le fun τ => (hfg τ).trans (by have := le_ciSup (bdd_of_abs g B hg) τ; linarith)

lemma abs_iSup_sub_le {T : Type*} [Nonempty T] (f g : T → ℝ) (B c : ℝ)
    (hf : ∀ τ, |f τ| ≤ B) (hg : ∀ τ, |g τ| ≤ B) (hfg : ∀ τ, |f τ - g τ| ≤ c) :
    |(⨆ τ, f τ) - ⨆ τ, g τ| ≤ c := by
  have h1 := iSup_le_iSup_add f g B c hg fun τ => by have := (abs_le.mp (hfg τ)).2; linarith
  have h2 := iSup_le_iSup_add g f B c hf fun τ => by have := (abs_le.mp (hfg τ)).1; linarith
  rw [abs_le]; constructor <;> linarith

lemma avg_abs_le {n : ℕ} (a : Fin n → ℝ) (K : ℝ) (hK : 0 ≤ K) (ha : ∀ i, |a i| ≤ K) :
    |(n : ℝ)⁻¹ * ∑ i, a i| ≤ K := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [hK]
  have hn : (0 : ℝ) < n := by exact_mod_cast h
  rw [abs_mul, abs_inv, abs_of_pos hn]
  have : |∑ i, a i| ≤ n * K := by
    calc |∑ i, a i| ≤ ∑ i, |a i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, K := Finset.sum_le_sum fun i _ => ha i
      _ = n * K := by simp
  calc (n : ℝ)⁻¹ * |∑ i, a i| ≤ (n : ℝ)⁻¹ * (n * K) := by gcongr
    _ = K := by field_simp

lemma signVec_abs {n : ℕ} (σ : Fin n → Bool) (i : Fin n) : |UnderstandingML.signVec σ i| = 1 := by
  unfold UnderstandingML.signVec; split_ifs <;> simp

lemma signVec_not {n : ℕ} (σ : Fin n → Bool) (i : Fin n) :
    UnderstandingML.signVec (fun j => !σ j) i = -UnderstandingML.signVec σ i := by
  unfold UnderstandingML.signVec; cases h : σ i <;> simp [h]

lemma sum_sign_abs {n : ℕ} (σ : Fin n → Bool) (a : Fin n → ℝ) (K : ℝ) (ha : ∀ i, |a i| ≤ K) :
    |∑ i, UnderstandingML.signVec σ i * a i| ≤ n * K := by
  calc |∑ i, UnderstandingML.signVec σ i * a i| ≤ ∑ i, |UnderstandingML.signVec σ i * a i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, K := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, signVec_abs, one_mul]; exact ha i
    _ = n * K := by simp

lemma sum_update {n : ℕ} {X : Type*} (h : X → ℝ) (s : Fin n → X) (i : Fin n) (z : X) :
    ∑ j, h (Function.update s i z j) = ∑ j, h (s j) + (h z - h (s i)) := by
  classical
  have : ∀ j, h (Function.update s i z j) = h (s j) + if j = i then h z - h (s i) else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mcd_mgf {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (c B : ℝ) (hc : 0 ≤ c) : ∀ (n : ℕ) (f : (Fin n → Ω) → ℝ), Measurable f →
    (∀ S, |f S| ≤ B) → (∀ S i z, |f (Function.update S i z) - f S| ≤ c) → ∀ t : ℝ,
    ∫ S, Real.exp (t * (f S - ∫ S', f S' ∂(Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν)
      ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) := by
  intro n
  induction n with
  | zero =>
    intro f _ _ _ t
    have hfS : ∀ S, f S = f default := fun S => congrArg f (Subsingleton.elim _ _)
    simp [hfS]
  | succ n ih =>
    intro f hf hB hdiff t
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => ν)
        (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have hmps := hmp.symm e
    set g : Ω → (Fin n → Ω) → ℝ := fun z w => f (Fin.cons z w) with hg
    have hge : ∀ p : Ω × (Fin n → Ω), f (e.symm p) = g p.1 p.2 := by
      intro p; simp [g, e]; try rfl
    have hgm : Measurable (Function.uncurry g) := by
      have : Function.uncurry g = fun p => f (e.symm p) := by
        funext p; rw [hge p]; rfl
      rw [this]; exact hf.comp e.symm.measurable
    have hgB : ∀ z w, |g z w| ≤ B := fun z w => hB _
    set hw : (Fin n → Ω) → ℝ := fun w => ∫ z, g z w ∂ν with hhw
    have hwm : Measurable hw :=
      (StronglyMeasurable.integral_prod_left (μ := ν) hgm.stronglyMeasurable).measurable
    have hwB : ∀ w, |hw w| ≤ B := fun w => abs_integral_le_of_bdd ν _ B fun z => hgB z w
    have hgz : ∀ w, Measurable fun z => g z w := fun w => hgm.comp (measurable_id.prodMk measurable_const)
    have hwdiff : ∀ w j y, |hw (Function.update w j y) - hw w| ≤ c := by
      intro w j y
      simp only [hw]
      rw [← integral_sub (int_of_bdd ν _ (hgz _) B fun z => hgB z _)
        (int_of_bdd ν _ (hgz _) B fun z => hgB z _)]
      refine abs_integral_le_of_bdd ν _ c fun z => ?_
      simp only [g, Fin.cons_update]
      exact hdiff _ _ _
    have hih := ih hw hwm hwB hwdiff t
    -- the mean
    have hint_f : Integrable (fun p : Ω × (Fin n → Ω) => g p.1 p.2) (ν.prod (Measure.pi fun _ => ν)) :=
      int_of_bdd _ _ hgm B fun p => hgB p.1 p.2
    have hmean : ∫ S, f S ∂(Measure.pi fun _ => ν) = ∫ w, hw w ∂(Measure.pi fun _ => ν) := by
      rw [← hmps.integral_comp' (g := f)]
      simp_rw [hge]
      rw [integral_prod_symm _ hint_f]
    obtain ⟨m, hm⟩ : ∃ m, m = ∫ S, f S ∂(Measure.pi fun _ => ν) := ⟨_, rfl⟩
    rw [← hm]
    rw [← hm] at hmean
    have hexpm : Measurable fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)) :=
      Real.measurable_exp.comp (measurable_const.mul (hgm.sub measurable_const))
    have hint_e : Integrable (fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)))
        (ν.prod (Measure.pi fun _ => ν)) :=
      int_of_bdd _ _ hexpm (Real.exp (|t| * (B + |m|))) fun p => by
        rw [abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hgB p.1 p.2
        calc t * (g p.1 p.2 - m) ≤ |t * (g p.1 p.2 - m)| := le_abs_self _
          _ = |t| * |g p.1 p.2 - m| := abs_mul _ _
          _ ≤ |t| * (B + |m|) := by
            gcongr
            calc |g p.1 p.2 - m| ≤ |g p.1 p.2| + |m| := abs_sub _ _
              _ ≤ B + |m| := by linarith
    have hstep : ∀ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ≤
        Real.exp (t * (hw w - m)) * Real.exp (c ^ 2 / 8 * t ^ 2) := by
      intro w
      have hosc : ∀ z z', g z' w - g z w ≤ c := by
        intro z z'
        have := hdiff (Fin.cons z w) 0 z'
        rw [Fin.update_cons_zero] at this
        exact (abs_le.mp this).2
      have hh := hoeff_step ν (fun z => g z w) (hgz w) c B hc (fun z => hgB z w) hosc t
      have : ∀ z, Real.exp (t * (g z w - m)) =
          Real.exp (t * (hw w - m)) * Real.exp (t * (g z w - ∫ z', g z' w ∂ν)) := by
        intro z; rw [← Real.exp_add]; congr 1; simp only [hw]; ring
      simp_rw [this]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    calc ∫ S, Real.exp (t * (f S - m)) ∂(Measure.pi fun _ => ν)
        = ∫ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ∂(Measure.pi fun _ => ν) := by
          rw [← hmps.integral_comp' (g := fun S => Real.exp (t * (f S - m)))]
          simp_rw [hge]
          rw [integral_prod_symm _ hint_e]
      _ ≤ ∫ w, Real.exp (t * (hw w - m)) * Real.exp (c ^ 2 / 8 * t ^ 2)
            ∂(Measure.pi fun _ => ν) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
            integral_nonneg fun z => (Real.exp_pos _).le) ?_ (Filter.Eventually.of_forall hstep)
          refine Integrable.mul_const ?_ _
          refine int_of_bdd _ _ (Real.measurable_exp.comp
            (measurable_const.mul (hwm.sub measurable_const))) (Real.exp (|t| * (B + |m|))) fun w => ?_
          rw [abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          have h1 := hwB w
          calc t * (hw w - m) ≤ |t * (hw w - m)| := le_abs_self _
            _ = |t| * |hw w - m| := abs_mul _ _
            _ ≤ |t| * (B + |m|) := by
              gcongr
              calc |hw w - m| ≤ |hw w| + |m| := abs_sub _ _
                _ ≤ B + |m| := by linarith
      _ = (∫ w, Real.exp (t * (hw w - ∫ w', hw w' ∂(Measure.pi fun _ => ν)))
            ∂(Measure.pi fun _ => ν)) * Real.exp (c ^ 2 / 8 * t ^ 2) := by
          rw [integral_mul_const, ← hmean]
      _ ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) * Real.exp (c ^ 2 / 8 * t ^ 2) :=
          mul_le_mul_of_nonneg_right hih (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * c ^ 2 / 8 * t ^ 2) := by
          rw [← Real.exp_add]; congr 1; push_cast; ring

/-- One-sided McDiarmid tail. -/
theorem mcd_tail {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (f : (Fin n → Ω) → ℝ) (hfm : Measurable f) (B : ℝ)
    (hfB : ∀ S, |f S| ≤ B) (c : ℝ) (hc : 0 < c)
    (hdiff : ∀ S i z, |f (Function.update S i z) - f S| ≤ c) (u : ℝ) (hu : 0 ≤ u) :
    (Measure.pi fun _ : Fin n => ν) {S | (∫ S', f S' ∂(Measure.pi fun _ => ν)) + u ≤ f S}
      ≤ ENNReal.ofReal (Real.exp (-(2 * u ^ 2) / (n * c ^ 2))) := by
  set π := Measure.pi fun _ : Fin n => ν with hπ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set cc : NNReal := ⟨n * c ^ 2 / 4, by positivity⟩ with hcc
  have hccr : (cc : ℝ) = n * c ^ 2 / 4 := rfl
  set Y : (Fin n → Ω) → ℝ := fun S => f S - ∫ S', f S' ∂π with hY
  have hEf : |∫ S', f S' ∂π| ≤ B := abs_integral_le_of_bdd π _ B hfB
  have hYm : Measurable Y := hfm.sub measurable_const
  have hsg : HasSubgaussianMGF Y cc π := by
    constructor
    · intro t
      refine int_of_bdd π _ (Real.measurable_exp.comp (measurable_const.mul hYm))
        (Real.exp (|t| * (2 * B))) fun S => ?_
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 := hfB S
      calc t * Y S ≤ |t * Y S| := le_abs_self _
        _ = |t| * |Y S| := abs_mul _ _
        _ ≤ |t| * (2 * B) := by
          gcongr
          calc |Y S| ≤ |f S| + |∫ S', f S' ∂π| := abs_sub _ _
            _ ≤ 2 * B := by linarith
    · intro t
      have := mcd_mgf ν c B hc.le n f hfm hfB hdiff t
      unfold mgf
      calc ∫ S, Real.exp (t * Y S) ∂π ≤ Real.exp (n * c ^ 2 / 8 * t ^ 2) := this
        _ = Real.exp (cc * t ^ 2 / 2) := by
          congr 1; rw [hccr]; ring
  have t1 := hsg.measure_ge_le hu
  have hexp : -u ^ 2 / (2 * (cc : ℝ)) = -(2 * u ^ 2) / (n * c ^ 2) := by
    rw [hccr]; field_simp; ring
  rw [hexp] at t1
  have hset : {S | (∫ S', f S' ∂π) + u ≤ f S} = {S | u ≤ Y S} := by
    ext S; simp only [Set.mem_setOf_eq, Y]; constructor <;> intro h <;> linarith
  rw [hset, ← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal t1

section Sym

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
  {T : Type*} [Countable T] [Nonempty T]

theorem mean_eq (g : X → ℝ) (hg : Measurable g) (M : ℝ) (hM : ∀ x, |g x| ≤ M) (n : ℕ)
    (hn : 0 < n) :
    ∫ x, g x ∂P = ∫ s, (n : ℝ)⁻¹ * ∑ i, g (s i) ∂(Measure.pi fun _ : Fin n => P) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [integral_const_mul, integral_finset_sum]
  · have : ∀ i : Fin n, ∫ s, g (s i) ∂(Measure.pi fun _ : Fin n => P) = ∫ x, g x ∂P := by
      intro i
      have h := (measurePreserving_eval (fun _ : Fin n => P) i)
      have := integral_map (μ := Measure.pi fun _ : Fin n => P) h.measurable.aemeasurable
        hg.aestronglyMeasurable
      rw [h.map_eq] at this
      exact this.symm
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro i _
    exact int_of_bdd _ _ (hg.comp (measurable_pi_apply i)) M fun s => hM (s i)

theorem sym (g : T → X → ℝ) (hg : ∀ τ, Measurable (g τ)) (M : ℝ) (hM : ∀ τ x, |g τ x| ≤ M)
    (n : ℕ) (hn : 0 < n) :
    ∫ s, (⨆ τ, (∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ i, g τ (s i))) ∂(Measure.pi fun _ : Fin n => P)
      ≤ 2 * ∫ s, (1 / (n : ℝ)) * ((1 / 2 ^ n) * ∑ σ : Fin n → Bool,
          ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)) ∂(Measure.pi fun _ : Fin n => P) := by
  classical
  set π := Measure.pi fun _ : Fin n => P with hπ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hM0 : 0 ≤ M := by
    obtain ⟨τ⟩ := ‹Nonempty T›
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure P
    exact (abs_nonneg _).trans (hM τ x)
  have hem : ∀ τ (s : Fin n → X), |(n : ℝ)⁻¹ * ∑ i, g τ (s i)| ≤ M :=
    fun τ s => avg_abs_le _ M hM0 fun i => hM τ (s i)
  have hemm : ∀ τ, Measurable fun s : Fin n → X => (n : ℝ)⁻¹ * ∑ i, g τ (s i) := fun τ =>
    measurable_const.mul (Finset.measurable_sum _ fun i _ => (hg τ).comp (measurable_pi_apply i))
  have hmu : ∀ τ, |∫ x, g τ x ∂P| ≤ M := fun τ => abs_integral_le_of_bdd P _ M (hM τ)
  -- the supremum Z
  set Z : (Fin n → X) → ℝ := fun s => ⨆ τ, (∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ i, g τ (s i))
    with hZ
  have hZm : Measurable Z := Measurable.iSup fun τ => measurable_const.sub (hemm τ)
  have hZb : ∀ s, |Z s| ≤ 2 * M := fun s => abs_iSup_le _ _ fun τ => by
    have h1 := hmu τ; have h2 := hem τ s
    rw [abs_le] at *; constructor <;> linarith
  -- the symmetrized supremum W
  set W : (Fin n → X) × (Fin n → X) → ℝ :=
    fun p => ⨆ τ, ((n : ℝ)⁻¹ * ∑ i, g τ (p.2 i) - (n : ℝ)⁻¹ * ∑ i, g τ (p.1 i)) with hW
  have hWt : ∀ τ (p : (Fin n → X) × (Fin n → X)),
      |(n : ℝ)⁻¹ * ∑ i, g τ (p.2 i) - (n : ℝ)⁻¹ * ∑ i, g τ (p.1 i)| ≤ 2 * M := by
    intro τ p
    have h1 := hem τ p.2; have h2 := hem τ p.1
    rw [abs_le] at *; constructor <;> linarith
  have hWm : Measurable W :=
    Measurable.iSup fun τ => ((hemm τ).comp measurable_snd).sub ((hemm τ).comp measurable_fst)
  have hWb : ∀ p, |W p| ≤ 2 * M := fun p => abs_iSup_le _ _ fun τ => hWt τ p
  have hWint : Integrable W (π.prod π) := int_of_bdd _ _ hWm _ hWb
  -- Step 1
  have hstep1 : ∀ s, Z s ≤ ∫ s', W (s, s') ∂π := by
    intro s
    apply ciSup_le
    intro τ
    calc ∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ i, g τ (s i)
        = ∫ s', ((n : ℝ)⁻¹ * ∑ i, g τ (s' i) - (n : ℝ)⁻¹ * ∑ i, g τ (s i)) ∂π := by
          rw [mean_eq P (g τ) (hg τ) M (hM τ) n hn, integral_sub
            (int_of_bdd _ _ (hemm τ) M (hem τ)) (integrable_const _), integral_const]
          simp [hπ]
      _ ≤ ∫ s', W (s, s') ∂π := by
          refine integral_mono (int_of_bdd _ _ ((hemm τ).sub measurable_const) (2 * M)
            fun s' => hWt τ (s, s')) (int_of_bdd _ _ (hWm.comp (measurable_const.prodMk
              measurable_id)) (2 * M) fun s' => hWb (s, s')) fun s' => ?_
          exact le_ciSup (bdd_of_abs _ _ fun τ => hWt τ (s, s')) τ
  have hstep2 : ∫ s, Z s ∂π ≤ ∫ p, W p ∂(π.prod π) := by
    rw [integral_prod W hWint]
    exact integral_mono (int_of_bdd _ _ hZm _ hZb) hWint.integral_prod_left hstep1
  -- Step 3: sign swaps
  set e := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin n) with he
  have hE : MeasurePreserving e (Measure.pi fun _ : Fin n => P.prod P) (π.prod π) :=
    measurePreserving_arrowProdEquivProdArrow X X (Fin n) (fun _ => P) (fun _ => P)
  set Φ : (Fin n → Bool) → (Fin n → X) × (Fin n → X) → (Fin n → X) × (Fin n → X) :=
    fun σ p => (fun i => if σ i then p.1 i else p.2 i, fun i => if σ i then p.2 i else p.1 i)
    with hΦ
  have hΦmp : ∀ σ, MeasurePreserving (Φ σ) (π.prod π) (π.prod π) := by
    intro σ
    have hpi : MeasurePreserving (fun (w : Fin n → X × X) i => if σ i then w i else (w i).swap)
        (Measure.pi fun _ : Fin n => P.prod P) (Measure.pi fun _ : Fin n => P.prod P) := by
      refine measurePreserving_pi (fun _ => P.prod P) (fun _ => P.prod P)
        (f := fun i (q : X × X) => if σ i then q else q.swap) fun i => ?_
      by_cases h : σ i = true
      · simp only [h, if_true]; exact MeasurePreserving.id _
      · simp only [h]; exact Measure.measurePreserving_swap
    have hcomp := hE.comp (hpi.comp (hE.symm e))
    have heq : Φ σ = e ∘ (fun (w : Fin n → X × X) i => if σ i then w i else (w i).swap) ∘ e.symm := by
      funext p
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        by_cases h : σ i = true <;>
        simp [Φ, h, e, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    rw [heq]; exact hcomp
  have hWΦ : ∀ σ p, W (Φ σ p) = ⨆ τ, ((n : ℝ)⁻¹ *
      ∑ i, UnderstandingML.signVec σ i * (g τ (p.2 i) - g τ (p.1 i))) := by
    intro σ p
    simp only [W, Φ]
    congr 1; funext τ
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold UnderstandingML.signVec
    by_cases h : σ i = true <;> simp [h]
  have hstep3 : ∫ p, W p ∂(π.prod π) =
      ∫ p, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p) ∂(π.prod π) := by
    have hint : ∀ σ, Integrable (fun p => W (Φ σ p)) (π.prod π) := fun σ =>
      int_of_bdd _ _ (hWm.comp (hΦmp σ).measurable) _ fun p => hWb _
    rw [integral_const_mul, integral_finset_sum _ fun σ _ => hint σ]
    have : ∀ σ, ∫ p, W (Φ σ p) ∂(π.prod π) = ∫ p, W p ∂(π.prod π) := by
      intro σ
      have h := integral_map (μ := π.prod π) (hΦmp σ).measurable.aemeasurable
        hWm.aestronglyMeasurable
      rw [(hΦmp σ).map_eq] at h
      exact h.symm
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  -- Step 4: pointwise bound
  set U : (Fin n → Bool) → (Fin n → X) → ℝ :=
    fun σ s => ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i) with hU
  have hUt : ∀ σ τ (s : Fin n → X), |∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ n * M :=
    fun σ τ s => sum_sign_abs σ _ M fun i => hM τ (s i)
  set R : (Fin n → X) → ℝ := fun s => (1 / (n : ℝ)) * ((1 / 2 ^ n) * ∑ σ, U σ s) with hR
  have hRm : Measurable R := by
    refine measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun σ _ => ?_))
    exact Measurable.iSup fun τ => Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((hg τ).comp (measurable_pi_apply i))
  have hUb : ∀ σ s, |U σ s| ≤ n * M := fun σ s => abs_iSup_le _ _ fun τ => hUt σ τ s
  have hRb : ∀ s, |R s| ≤ M := by
    intro s
    simp only [R]
    have h2 : |(1 / 2 ^ n : ℝ) * ∑ σ, U σ s| ≤ n * M := by
      rw [abs_mul, abs_of_pos (by positivity)]
      calc (1 / 2 ^ n : ℝ) * |∑ σ, U σ s| ≤ (1 / 2 ^ n) * ∑ σ : Fin n → Bool, |U σ s| := by
            gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (1 / 2 ^ n) * ∑ _σ : Fin n → Bool, (n * M) := by
            gcongr with σ; exact hUb σ s
        _ = n * M := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast; field_simp
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (n : ℝ) * |(1 / 2 ^ n : ℝ) * ∑ σ, U σ s| ≤ 1 / n * (n * M) := by gcongr
      _ = M := by field_simp
  have hnot : ∀ s, ∑ σ : Fin n → Bool, U (fun j => !σ j) s = ∑ σ, U σ s := by
    intro s
    refine Fintype.sum_equiv ⟨fun σ j => !σ j, fun σ j => !σ j, fun σ => by funext j; simp,
      fun σ => by funext j; simp⟩ _ _ fun σ => rfl
  have hstep4 : ∀ p, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p) ≤ R p.2 + R p.1 := by
    intro p
    have hb : ∀ σ, W (Φ σ p) ≤ (n : ℝ)⁻¹ * U σ p.2 + (n : ℝ)⁻¹ * U (fun j => !σ j) p.1 := by
      intro σ
      rw [hWΦ]
      refine ciSup_le fun τ => ?_
      have hsplit : (n : ℝ)⁻¹ * ∑ i, UnderstandingML.signVec σ i * (g τ (p.2 i) - g τ (p.1 i)) =
          (n : ℝ)⁻¹ * ∑ i, UnderstandingML.signVec σ i * g τ (p.2 i) +
          (n : ℝ)⁻¹ * ∑ i, UnderstandingML.signVec (fun j => !σ j) i * g τ (p.1 i) := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [signVec_not]; ring
      rw [hsplit]
      have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnpos.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_ciSup (bdd_of_abs _ _ fun τ => hUt σ τ p.2) τ) hinv)
        (mul_le_mul_of_nonneg_left
          (le_ciSup (bdd_of_abs _ _ fun τ => hUt (fun j => !σ j) τ p.1) τ) hinv)
    calc (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p)
        ≤ (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
            ((n : ℝ)⁻¹ * U σ p.2 + (n : ℝ)⁻¹ * U (fun j => !σ j) p.1) := by
          gcongr with σ; exact hb σ
      _ = R p.2 + R p.1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnot]
          simp only [R]; ring
  -- Step 5
  have hRint : Integrable R π := int_of_bdd _ _ hRm M hRb
  have hfst : ∫ p, R p.1 ∂(π.prod π) = ∫ s, R s ∂π := by
    have h := integral_map (μ := π.prod π) (measurePreserving_fst (μ := π) (ν := π)).measurable.aemeasurable
      hRm.aestronglyMeasurable
    rw [(measurePreserving_fst (μ := π) (ν := π)).map_eq] at h
    exact h.symm
  have hsnd : ∫ p, R p.2 ∂(π.prod π) = ∫ s, R s ∂π := by
    have h := integral_map (μ := π.prod π) (measurePreserving_snd (μ := π) (ν := π)).measurable.aemeasurable
      hRm.aestronglyMeasurable
    rw [(measurePreserving_snd (μ := π) (ν := π)).map_eq] at h
    exact h.symm
  have hstep5 : ∫ p, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p) ∂(π.prod π) ≤
      2 * ∫ s, R s ∂π := by
    have hi1 : Integrable (fun p : (Fin n → X) × (Fin n → X) => R p.2) (π.prod π) :=
      int_of_bdd _ _ (hRm.comp measurable_snd) M fun p => hRb _
    have hi2 : Integrable (fun p : (Fin n → X) × (Fin n → X) => R p.1) (π.prod π) :=
      int_of_bdd _ _ (hRm.comp measurable_fst) M fun p => hRb _
    calc ∫ p, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, W (Φ σ p) ∂(π.prod π)
        ≤ ∫ p, (R p.2 + R p.1) ∂(π.prod π) := by
          refine integral_mono ?_ (hi1.add hi2) hstep4
          refine Integrable.const_mul ?_ _
          exact integrable_finset_sum _ fun σ _ =>
            int_of_bdd _ _ (hWm.comp (hΦmp σ).measurable) _ fun p => hWb _
      _ = 2 * ∫ s, R s ∂π := by
          rw [integral_add hi1 hi2, hfst, hsnd]; ring
  calc ∫ s, Z s ∂π ≤ ∫ p, W p ∂(π.prod π) := hstep2
    _ = _ := hstep3
    _ ≤ 2 * ∫ s, R s ∂π := hstep5

end Sym

end F198

namespace F198

open P82cd VarianceRegularization.FastRates

theorem rad_int {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    {T : Type*} [Countable T] [Nonempty T]
    (g : T → X → ℝ) (hg : ∀ τ, Measurable (g τ)) (M : ℝ) (hM : ∀ τ x, |g τ x| ≤ M)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun s : Fin n → X => (1 / (n : ℝ)) * ((1 / 2 ^ n) * ∑ σ : Fin n → Bool,
          ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i))) (Measure.pi fun _ : Fin n => P) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hUt : ∀ σ τ (s : Fin n → X), |∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ n * M :=
    fun σ τ s => sum_sign_abs σ _ M fun i => hM τ (s i)
  have hUb : ∀ σ (s : Fin n → X), |⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ n * M :=
    fun σ s => abs_iSup_le _ _ fun τ => hUt σ τ s
  refine int_of_bdd _ _ ?_ M fun s => ?_
  · refine measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun σ _ => ?_))
    exact Measurable.iSup fun τ => Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((hg τ).comp (measurable_pi_apply i))
  · have h2 : |(1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ n * M := by
      rw [abs_mul, abs_of_pos (by positivity)]
      calc (1 / 2 ^ n : ℝ) * |∑ σ : Fin n → Bool,
            ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)|
          ≤ (1 / 2 ^ n) * ∑ σ : Fin n → Bool,
            |⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)| := by
            gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (1 / 2 ^ n) * ∑ _σ : Fin n → Bool, (n * M) := by
            gcongr with σ; exact hUb σ s
        _ = n * M := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast; field_simp
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (n : ℝ) * |(1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
          ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)| ≤ 1 / n * (n * M) := by gcongr
      _ = M := by field_simp

theorem norm_le_R {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (lam γ ε : ℝ) (hlam : 0 < lam)
    (hγ : 1 < γ) (h : lam * ‖v‖ ^ γ ≤ 2 * ε) : ‖v‖ ≤ (2 * ε / lam) ^ (1 / γ) := by
  have hγ0 : 0 < γ := by linarith
  have h1 : ‖v‖ ^ γ ≤ 2 * ε / lam := by rw [le_div_iff₀ hlam]; linarith
  have h2 : ‖v‖ = (‖v‖ ^ γ) ^ (1 / γ) := by
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hγ0.ne', Real.rpow_one]
  rw [h2]
  exact Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) h1 (by positivity)

theorem main
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
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (t : ℝ) (ht : 0 < t)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ (1 / 2) * lam * r ^ γ)
    (hRint : Integrable (fun s : Fin n → X => localizedRademacher Θ ℓ P (subOptSet Θ ℓ P (2 * ε)) s)
      (Measure.pi (fun _ : Fin n => P)))
    (h27a : (2 * (8 ^ γ * L ^ γ) / lam) ^ (1 / (γ - 1)) * (ρ / n) ^ (γ / (2 * (γ - 1))) ≤ ε)
    (h27b : 2 * (∫ s, localizedRademacher Θ ℓ P (subOptSet Θ ℓ P (2 * ε)) s
                ∂(Measure.pi (fun _ : Fin n => P)))
              + L * (2 * ε / lam) ^ (1 / γ) * Real.sqrt (2 * t / n) ≤ ε / 2) :
    Measure.pi (fun _ : Fin n => P) {s | ¬ empSubOptSet Θ ρ ℓ s ε ⊆ subOptSet Θ ℓ P (2 * ε)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  classical
  have hdev := (d44_dev P Θ hΘ ℓ L hL hconv hlip hmeas hint hS_ne hS_closed lam γ r hlam hγ hr
    hgrowth n hn ρ hρ ε hε hεr h27a).2
  refine hdev.trans ?_
  set π := Measure.pi (fun _ : Fin n => P) with hπ
  set S0 := subOptSet Θ ℓ P 0 with hS0
  set A := subOptSet Θ ℓ P (2 * ε) with hA
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hAΘ : ∀ θ ∈ A, θ ∈ Θ := fun θ h => h.1
  have hS0Θ : ∀ θ ∈ S0, θ ∈ Θ := fun θ h => h.1
  have hprojS : ∀ θ, proj S0 θ ∈ S0 := fun θ => (D44A60D6.proj_spec S0 hS_closed hS_ne θ).1
  set R := (2 * ε / lam) ^ (1 / γ) with hR
  have hRpos : 0 < R := Real.rpow_pos_of_pos (by positivity) _
  have hdist : ∀ θ ∈ A, ‖θ - proj S0 θ‖ ≤ R := fun θ hθ => norm_le_R _ lam γ ε hlam hγ
      (D44A60D6.dist_bound P Θ hΘ ℓ hconv hint hS_ne hS_closed lam γ r hr hgrowth ε hε hεr θ hθ)
  set M := L * R with hM
  have hgb : ∀ θ ∈ A, ∀ x, |ℓ θ x - ℓ (proj S0 θ) x| ≤ M := fun θ hθ x =>
    (hlip x θ (hAΘ θ hθ) _ (hS0Θ _ (hprojS θ))).trans (mul_le_mul_of_nonneg_left (hdist θ hθ) hL)
  rcases hL.lt_or_eq with hLpos | hL0
  swap
  · calc π {s | ∀ δ > 0, ∃ θ ∈ A, ε / 2 - δ ≤ localizedDeviation Θ ℓ P s θ}
        ≤ π ∅ := measure_mono fun s hs => by
          obtain ⟨θ, hθ, hle⟩ := hs (ε / 4) (by positivity)
          have h0 : ∀ x, ℓ θ x - ℓ (proj S0 θ) x = 0 := fun x => by
            have := hgb θ hθ x
            rw [hM, ← hL0, zero_mul] at this
            exact abs_nonpos_iff.mp this
          have hz : localizedDeviation Θ ℓ P s θ = 0 := by
            unfold localizedDeviation
            simp only [← hS0, h0]
            simp [VarianceRegularization.Expansion.empMean]
          linarith
      _ = 0 := measure_empty
      _ ≤ _ := bot_le
  have hMpos : 0 < M := mul_pos hLpos hRpos
  have hM0 : 0 ≤ M := hMpos.le
  set Sp : Set (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
    (fun θ => (θ, proj S0 θ)) '' A with hSp
  have hS0A : S0 ⊆ A := fun θ hθ => ⟨hθ.1, fun θ' h' => by have := hθ.2 θ' h'; linarith⟩
  haveI : Nonempty Sp := ⟨⟨_, hS_ne.some, hS0A hS_ne.some_mem, rfl⟩⟩
  obtain ⟨C, hCc, hCd⟩ := TopologicalSpace.exists_countable_dense Sp
  haveI : Countable C := hCc.to_subtype
  haveI : Nonempty C := hCd.nonempty.to_subtype
  set g : C → X → ℝ := fun τ x => ℓ τ.1.1.1 x - ℓ τ.1.1.2 x with hg
  have hτ : ∀ τ : C, τ.1.1.1 ∈ Θ ∧ τ.1.1.2 ∈ Θ ∧ (∀ x, |g τ x| ≤ M) ∧
      (fun x => g τ x) ∈ localizedClass Θ ℓ P A := by
    intro τ
    obtain ⟨θ, hθ, heq⟩ := τ.1.2
    have e1 : τ.1.1.1 = θ := by rw [← heq]
    have e2 : τ.1.1.2 = proj S0 θ := by rw [← heq]
    refine ⟨by rw [e1]; exact hAΘ θ hθ, by rw [e2]; exact hS0Θ _ (hprojS θ), fun x => ?_,
      ⟨θ, hθ, ?_⟩⟩
    · simp only [g, e1, e2]; exact hgb θ hθ x
    · funext x; show ℓ τ.1.1.1 x - ℓ τ.1.1.2 x = _; rw [e1, e2]
  have hgm : ∀ τ, Measurable (g τ) := fun τ =>
    (hmeas _ (hτ τ).1).sub (hmeas _ (hτ τ).2.1)
  have hgM : ∀ τ x, |g τ x| ≤ M := fun τ => (hτ τ).2.2.1
  have hgi : ∀ τ, Integrable (g τ) P := fun τ =>
    (hint _ (hτ τ).1).sub (hint _ (hτ τ).2.1)
  set Z : (Fin n → X) → ℝ := fun s => ⨆ τ, (∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ i, g τ (s i)) with hZ
  have hem : ∀ τ (s : Fin n → X), |(n : ℝ)⁻¹ * ∑ i, g τ (s i)| ≤ M :=
    fun τ s => avg_abs_le _ M hM0 fun i => hgM τ (s i)
  have hterm : ∀ τ (s : Fin n → X), |∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ i, g τ (s i)| ≤ 2 * M := by
    intro τ s
    have h1 := abs_integral_le_of_bdd P _ M (hgM τ); have h2 := hem τ s
    rw [abs_le] at *; constructor <;> linarith
  have hZm : Measurable Z := Measurable.iSup fun τ => measurable_const.sub
    (measurable_const.mul (Finset.measurable_sum _ fun i _ => (hgm τ).comp (measurable_pi_apply i)))
  have hZb : ∀ s, |Z s| ≤ 2 * M := fun s => abs_iSup_le _ _ fun τ => hterm τ s
  have hZdiff : ∀ s i z, |Z (Function.update s i z) - Z s| ≤ 2 * M / n := by
    intro s i z
    refine abs_iSup_sub_le _ _ (2 * M) _ (fun τ => hterm τ _) (fun τ => hterm τ s) fun τ => ?_
    have heq : (∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ j, g τ (Function.update s i z j)) -
        (∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ j, g τ (s j)) = -((n : ℝ)⁻¹ * (g τ z - g τ (s i))) := by
      rw [sum_update (g τ) s i z]; ring
    rw [heq, abs_neg, abs_mul, abs_inv, abs_of_pos hnpos]
    have hb : |g τ z - g τ (s i)| ≤ 2 * M := by
      have h1 := hgM τ z; have h2 := hgM τ (s i)
      rw [abs_le] at *; constructor <;> linarith
    calc (n : ℝ)⁻¹ * |g τ z - g τ (s i)| ≤ (n : ℝ)⁻¹ * (2 * M) := by gcongr
      _ = 2 * M / n := by ring
  -- symmetrization and comparison with the localized Rademacher complexity
  have hsym := sym P g hgm M hgM n hn
  have hRadle : ∀ s : Fin n → X, (1 / (n : ℝ)) * ((1 / 2 ^ n) * ∑ σ : Fin n → Bool,
      ⨆ τ, ∑ i, UnderstandingML.signVec σ i * g τ (s i)) ≤ localizedRademacher Θ ℓ P A s := by
    intro s
    unfold localizedRademacher UnderstandingML.rademacher
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun σ _ => ?_) (by positivity)) (by positivity)
    have hbdd : BddAbove (Set.range fun a : UnderstandingML.evalSet (localizedClass Θ ℓ P A) s =>
        ∑ i, UnderstandingML.signVec σ i * (a : Fin n → ℝ) i) := by
      refine bdd_of_abs _ (n * M) fun a => ?_
      obtain ⟨f, ⟨θ, hθ, rfl⟩, hfa⟩ := a.2
      rw [hfa]; exact sum_sign_abs σ _ M fun i => hgb θ hθ (s i)
    refine ciSup_le fun τ => ?_
    exact le_ciSup hbdd ⟨fun i => g τ (s i), fun x => g τ x, (hτ τ).2.2.2, rfl⟩
  have hRadI := integral_mono (rad_int P g hgm M hgM n hn) hRint hRadle
  -- the event lies in {Z ≥ ε/2}
  have hev : ∀ s : Fin n → X, (∀ δ > 0, ∃ θ ∈ A, ε / 2 - δ ≤ localizedDeviation Θ ℓ P s θ) →
      ε / 2 ≤ Z s := by
    intro s hs
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨θ, hθ, hle⟩ := hs (η / 2) (by positivity)
    set η' := η / (8 * L) with hη'
    have hη'pos : 0 < η' := by positivity
    obtain ⟨c, hcC, hcd⟩ := hCd.exists_dist_lt
      (⟨(θ, proj S0 θ), θ, hθ, rfl⟩ : Sp) hη'pos
    set τ : C := ⟨c, hcC⟩ with hτdef
    obtain ⟨h1, h2, -, -⟩ := hτ τ
    rw [Subtype.dist_eq, Prod.dist_eq, max_lt_iff] at hcd
    obtain ⟨d1, d2⟩ := hcd
    have d1' : ‖c.1.1 - θ‖ < η' := by rw [← dist_eq_norm, dist_comm]; exact d1
    have d2' : ‖c.1.2 - proj S0 θ‖ < η' := by rw [← dist_eq_norm, dist_comm]; exact d2
    have hθΘ := hAΘ θ hθ
    have hpΘ := hS0Θ _ (hprojS θ)
    have hpt : ∀ x, |g τ x - (ℓ θ x - ℓ (proj S0 θ) x)| ≤ 2 * L * η' := by
      intro x
      have a1 := (hlip x _ h1 θ hθΘ).trans (mul_le_mul_of_nonneg_left d1'.le hL)
      have a2 := (hlip x _ h2 _ hpΘ).trans (mul_le_mul_of_nonneg_left d2'.le hL)
      simp only [g]
      rw [abs_le] at *; constructor <;> linarith
    have hη2 : 0 ≤ 2 * L * η' := by positivity
    have hI : |∫ x, g τ x ∂P - ∫ x, (ℓ θ x - ℓ (proj S0 θ) x) ∂P| ≤ 2 * L * η' := by
      have hs := integral_sub (hgi τ) ((hint θ hθΘ).sub (hint _ hpΘ))
      simp only [Pi.sub_apply] at hs
      rw [← hs]
      exact abs_integral_le_of_bdd P _ _ hpt
    have hAv : |(n : ℝ)⁻¹ * ∑ i, g τ (s i) -
        (n : ℝ)⁻¹ * ∑ i, (ℓ θ (s i) - ℓ (proj S0 θ) (s i))| ≤ 2 * L * η' := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      exact avg_abs_le _ _ hη2 fun i => hpt (s i)
    have hZge : ∫ x, g τ x ∂P - (n : ℝ)⁻¹ * ∑ i, g τ (s i) ≤ Z s :=
      le_ciSup (bdd_of_abs _ _ fun τ => hterm τ s) τ
    have hΔ : localizedDeviation Θ ℓ P s θ = ∫ x, (ℓ θ x - ℓ (proj S0 θ) x) ∂P -
        (n : ℝ)⁻¹ * ∑ i, (ℓ θ (s i) - ℓ (proj S0 θ) (s i)) := by
      unfold localizedDeviation VarianceRegularization.Expansion.empMean; rfl
    have h4 : 4 * L * η' = η / 2 := by rw [hη']; field_simp; ring
    rw [abs_le] at hI hAv
    linarith [hI.1, hAv.2]
  set u := ε / 2 - ∫ s, Z s ∂π with hu
  have hu_ge : M * Real.sqrt (2 * t / n) ≤ u := by
    simp only [hu]
    have := hsym
    linarith
  have hu0 : 0 ≤ u := le_trans (by positivity) hu_ge
  calc π {s | ∀ δ > 0, ∃ θ ∈ A, ε / 2 - δ ≤ localizedDeviation Θ ℓ P s θ}
      ≤ π {s | (∫ s', Z s' ∂π) + u ≤ Z s} := measure_mono fun s hs => by
        have := hev s hs
        change (∫ s', Z s' ∂π) + u ≤ Z s
        simp only [hu]; linarith
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * u ^ 2) / (n * (2 * M / n) ^ 2))) :=
        mcd_tail P n hn Z hZm (2 * M) hZb (2 * M / n) (by positivity) hZdiff u hu0
    _ ≤ ENNReal.ofReal (Real.exp (-t)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hsq : Real.sqrt (2 * t / n) ^ 2 = 2 * t / n := Real.sq_sqrt (by positivity)
        have hu2 : M ^ 2 * (2 * t / n) ≤ u ^ 2 := by
          rw [← hsq, ← mul_pow]
          exact pow_le_pow_left₀ (by positivity) hu_ge 2
        have hden : (n : ℝ) * (2 * M / n) ^ 2 = 4 * M ^ 2 / n := by field_simp; ring
        rw [hden, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
        have : t * (4 * M ^ 2 / n) = 2 * (M ^ 2 * (2 * t / n)) := by ring
        rw [this]; linarith

end F198

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
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 ≤ ρ) (t : ℝ) (ht : 0 < t)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ (1 / 2) * lam * r ^ γ)
    (hRint : Integrable (fun s : Fin n → X => localizedRademacher Θ ℓ P (subOptSet Θ ℓ P (2 * ε)) s)
      (Measure.pi (fun _ : Fin n => P)))
    (h27a : (2 * (8 ^ γ * L ^ γ) / lam) ^ (1 / (γ - 1)) * (ρ / n) ^ (γ / (2 * (γ - 1))) ≤ ε)
    (h27b : 2 * (∫ s, localizedRademacher Θ ℓ P (subOptSet Θ ℓ P (2 * ε)) s
                ∂(Measure.pi (fun _ : Fin n => P)))
              + L * (2 * ε / lam) ^ (1 / γ) * Real.sqrt (2 * t / n) ≤ ε / 2) :
    Measure.pi (fun _ : Fin n => P) {s | ¬ empSubOptSet Θ ρ ℓ s ε ⊆ subOptSet Θ ℓ P (2 * ε)}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by
  exact F198.main P Θ hΘ ℓ L hL hconv hlip hmeas hint hS_ne hS_closed lam γ r hlam hγ hr hgrowth
    n hn ρ hρ t ht ε hε hεr hRint h27a h27b
