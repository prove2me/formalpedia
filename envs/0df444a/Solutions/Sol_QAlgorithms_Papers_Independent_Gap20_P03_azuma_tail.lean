-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.azuma_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:44:01.089046+00:00
-- url     : https://prove2.me/submissions/6e9a32de-6342-4b29-94b2-0603ee40eff8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable


theorem g73a_cvx (t c x : ℝ) (hc : 0 < c) (hx : |x| ≤ c) :
    Real.exp (t * x) ≤ Real.cosh (t*c) + x / c * Real.sinh (t*c) := by
  rw [abs_le] at hx
  have h1 : -1 ≤ x/c := by rw [le_div_iff₀ hc]; linarith
  have h2 : x/c ≤ 1 := by rw [div_le_iff₀ hc]; linarith
  have ha : 0 ≤ (1 + x/c)/2 := by linarith
  have hb : 0 ≤ (1 - x/c)/2 := by linarith
  have h := convexOn_exp.2 (Set.mem_univ (t*c)) (Set.mem_univ (-(t*c))) ha hb (by ring)
  simp only [smul_eq_mul] at h
  have e1 : (1 + x/c)/2 * (t*c) + (1 - x/c)/2 * (-(t*c)) = t * x := by field_simp; ring
  rw [e1] at h
  rw [Real.cosh_eq, Real.sinh_eq]
  calc _ ≤ _ := h
    _ = _ := by ring

theorem g73a_mgf {W : Type*} [MeasurableSpace W] (mu : Measure W)
    [IsProbabilityMeasure mu] (n : ℕ) (R : Fin n → W → ℝ)
    (hR : MartingaleDifferences mu R) (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (hall : ∀ᵐ w ∂mu, ∀ i, |R i w| ≤ c) :
    ∀ k (hk : k ≤ n),
      Integrable (fun w => Real.exp (t * ∑ j : Fin k, R ⟨j, lt_of_lt_of_le j.isLt hk⟩ w)) mu ∧
      ∫ w, Real.exp (t * ∑ j : Fin k, R ⟨j, lt_of_lt_of_le j.isLt hk⟩ w) ∂mu
        ≤ Real.cosh (t*c) ^ k := by
  have hmeas : ∀ i, Measurable (R i) := fun i => (hR i).1
  have hint_of : ∀ k (hk : k ≤ n),
      Integrable (fun w => Real.exp (t * ∑ j : Fin k, R ⟨j, lt_of_lt_of_le j.isLt hk⟩ w)) mu := by
    intro k hk
    refine Integrable.of_bound ?_ (Real.exp (t * (k * c))) ?_
    · apply Measurable.aestronglyMeasurable
      apply Measurable.exp; apply Measurable.const_mul
      exact Finset.measurable_sum _ (fun j _ => hmeas _)
    · filter_upwards [hall] with w hw
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ ht
      calc _ ≤ ∑ j : Fin k, |R ⟨j, lt_of_lt_of_le j.isLt hk⟩ w| :=
            le_trans (le_abs_self _) (Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ j : Fin k, c := Finset.sum_le_sum (fun j _ => hw _)
        _ = k * c := by simp
  intro k
  induction k with
  | zero => intro hk; refine ⟨hint_of 0 hk, ?_⟩; simp
  | succ k ih =>
    intro hk
    refine ⟨hint_of (k+1) hk, ?_⟩
    have hk' : k ≤ n := by omega
    obtain ⟨hFi, hFle⟩ := ih hk'
    set i : Fin n := ⟨k, by omega⟩ with hi
    set F : W → ℝ := fun w => Real.exp (t * ∑ j : Fin k, R ⟨j, lt_of_lt_of_le j.isLt hk'⟩ w)
      with hF
    have hsplit : (fun w => Real.exp (t * ∑ j : Fin (k+1), R ⟨j, lt_of_lt_of_le j.isLt hk⟩ w))
        = fun w => F w * Real.exp (t * R i w) := by
      funext w
      rw [Fin.sum_univ_castSucc, mul_add, Real.exp_add]
      rfl
    rw [hsplit]
    have hRi : Integrable (R i) mu := (hR i).2.1
    have hFm : Measurable F := by
      apply Measurable.exp; apply Measurable.const_mul
      exact Finset.measurable_sum _ (fun j _ => hmeas _)
    have hFbd : ∀ᵐ w ∂mu, ‖F w‖ ≤ Real.exp (t * (k * c)) := by
      filter_upwards [hall] with w hw
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ ht
      calc _ ≤ ∑ j : Fin k, |R ⟨j, lt_of_lt_of_le j.isLt hk'⟩ w| :=
            le_trans (le_abs_self _) (Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ j : Fin k, c := Finset.sum_le_sum (fun j _ => hw _)
        _ = k * c := by simp
    have hFR : Integrable (fun w => F w * R i w) mu :=
      hRi.bdd_mul hFm.aestronglyMeasurable hFbd
    -- the key martingale identity
    have hzero : ∫ w, F w * R i w ∂mu = 0 := by
      have hm : previousSigma R i ≤ ‹MeasurableSpace W› := (hR i).2.2.1
      have hFm' : Measurable[previousSigma R i] F := by
        have hg : Measurable (fun v : Fin k → ℝ => Real.exp (t * ∑ j, v j)) := by fun_prop
        exact hg.comp (comap_measurable _)
      have h1 := condExp_mul_of_stronglyMeasurable_left (μ := mu) (m := previousSigma R i)
        hFm'.stronglyMeasurable hFR hRi
      have h2 := (hR i).2.2.2
      calc ∫ w, F w * R i w ∂mu = ∫ w, (mu[F * R i | previousSigma R i]) w ∂mu :=
            (integral_condExp hm).symm
        _ = ∫ w, (0:ℝ) ∂mu := by
            apply integral_congr_ae
            filter_upwards [h1, h2] with w hw1 hw2
            rw [hw1]; simp [hw2]
        _ = 0 := by simp
    have hbound : ∀ᵐ w ∂mu, F w * Real.exp (t * R i w) ≤
        Real.cosh (t*c) * F w + Real.sinh (t*c) / c * (F w * R i w) := by
      filter_upwards [hall] with w hw
      have := g73a_cvx t c (R i w) hc (hw i)
      have hF0 : 0 ≤ F w := (Real.exp_pos _).le
      calc F w * Real.exp (t * R i w) ≤ F w * (Real.cosh (t*c) + R i w / c * Real.sinh (t*c)) :=
            mul_le_mul_of_nonneg_left this hF0
        _ = _ := by ring
    have hint2 : Integrable (fun w => Real.cosh (t*c) * F w + Real.sinh (t*c) / c * (F w * R i w)) mu :=
      (hFi.const_mul _).add (hFR.const_mul _)
    have hint1 : Integrable (fun w => F w * Real.exp (t * R i w)) mu := by
      have := hint_of (k+1) hk
      rw [hsplit] at this; exact this
    calc ∫ w, F w * Real.exp (t * R i w) ∂mu
        ≤ ∫ w, (Real.cosh (t*c) * F w + Real.sinh (t*c) / c * (F w * R i w)) ∂mu :=
          integral_mono_ae hint1 hint2 hbound
      _ = Real.cosh (t*c) * ∫ w, F w ∂mu := by
          rw [integral_add (hFi.const_mul _) (hFR.const_mul _), integral_const_mul,
            integral_const_mul, hzero]; ring
      _ ≤ Real.cosh (t*c) * Real.cosh (t*c) ^ k :=
          mul_le_mul_of_nonneg_left hFle (Real.cosh_pos _).le
      _ = Real.cosh (t*c) ^ (k+1) := by ring

/-- Lemma 2.3, p.6: positive-c Azuma bound, and the deterministic c=0
interpretation separately. n=0 has the probability-one empty-sum event. -/
theorem solution {W : Type*} [MeasurableSpace W] (mu : Measure W)
    [IsProbabilityMeasure mu] (n : ℕ) (R : Fin n → W → ℝ)
    (hR : MartingaleDifferences mu R) (c lambda : ℝ) (hc : 0 ≤ c)
    (hbounded : ∀ i, ∀ᵐ w ∂mu, |R i w| ≤ c) (hlambda : 0 < lambda) :
    (0 < c → mu {w | lambda*n ≤ ∑ i, R i w} ≤
      ENNReal.ofReal (Real.exp (-(lambda^2*n)/(2*c^2)))) ∧
    (c = 0 → mu {w | lambda*n ≤ ∑ i, R i w} = if n = 0 then 1 else 0) := by
  have hall : ∀ᵐ w ∂mu, ∀ i, |R i w| ≤ c := ae_all_iff.mpr hbounded
  constructor
  · intro hcpos
    set t := lambda / c^2 with ht_def
    have ht : 0 ≤ t := by positivity
    obtain ⟨hint, hle⟩ := g73a_mgf mu n R hR c t hcpos ht hall n le_rfl
    have hch := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := mu) (X := fun w => ∑ i, R i w) (lambda * n) ht hint
    unfold ProbabilityTheory.mgf at hch
    have hfinal : Real.exp (-t * (lambda * n)) * ∫ w, Real.exp (t * ∑ i, R i w) ∂mu ≤
        Real.exp (-(lambda^2*n)/(2*c^2)) := by
      calc _ ≤ Real.exp (-t * (lambda * n)) * Real.cosh (t*c) ^ n :=
            mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
        _ ≤ Real.exp (-t * (lambda * n)) * Real.exp ((t*c)^2/2) ^ n :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) n)
              (Real.exp_pos _).le
        _ = Real.exp (-t * (lambda * n) + n * ((t*c)^2/2)) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
        _ = Real.exp (-(lambda^2*n)/(2*c^2)) := by
            congr 1; rw [ht_def]; field_simp; ring
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (le_trans hch hfinal)
  · intro hc0
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      apply measure_mono_null (t := {w | ¬ ∀ i, |R i w| ≤ c})
      · intro w hw
        simp only [Set.mem_ofPred_eq] at hw ⊢
        intro hall'
        have : ∑ i, R i w = 0 := by
          apply Finset.sum_eq_zero; intro i _
          have := hall' i; rw [hc0] at this; exact abs_nonpos_iff.mp this
        rw [this] at hw
        have : 0 < lambda * n := mul_pos hlambda (by exact_mod_cast Nat.pos_of_ne_zero hn)
        linarith
      · exact ae_iff.mp hall


end
