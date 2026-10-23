-- Prove2me | solution 1 for StoneRegression.Criterion.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:04:42.235683+00:00
-- url     : https://prove2.me/submissions/5cebbaf2-6c4c-44d5-adad-1a390fc8ba2d

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction


namespace StoneRegression.Criterion

lemma p7_meas_wAt {d : ℕ} (W : WeightSeq d) (hW : MeasurableWeights W) (n : ℕ) (i : Fin n) :
    Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) => wAt W n ω i) := by
  have h1 : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) => (ω 0, sample ω n)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ (fun j => measurable_pi_apply _))
  exact (measurable_pi_apply i).comp ((hW n).comp h1)

lemma p7_map_eval {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (j : ℕ) : (xLaw μ).map (fun ω => ω j) = μ :=
  Measure.infinitePi_map_eval (fun _ : ℕ => μ) j

noncomputable def p7nu {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (n : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  ∑ i : Fin n, ((xLaw μ).withDensity (fun ω => ENNReal.ofReal (wAt W n ω i))).map
    (fun ω => ω (i.val + 1))

lemma p7nu_lintegral {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (n : ℕ)
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g x ∂(p7nu μ W n) =
      ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (wAt W n ω i) * g (ω (i.val + 1)) ∂(xLaw μ) := by
  unfold p7nu
  rw [lintegral_finsetSum_measure, lintegral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [lintegral_map hg (measurable_pi_apply (i.val + 1))]
    exact lintegral_withDensity_eq_lintegral_mul _
      (ENNReal.measurable_ofReal.comp (p7_meas_wAt W hW n i)) (hg.comp (measurable_pi_apply (i.val + 1)))
  · intro i _
    exact (ENNReal.measurable_ofReal.comp (p7_meas_wAt W hW n i)).mul
      (hg.comp (measurable_pi_apply _))

lemma p7nu_ac {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (n : ℕ) : p7nu μ W n ≪ μ := by
  intro s hs
  unfold p7nu
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hac : ((xLaw μ).withDensity (fun ω => ENNReal.ofReal (wAt W n ω i))).map
      (fun ω => ω (i.val + 1)) ≪ (xLaw μ).map (fun ω => ω (i.val + 1)) :=
    (withDensity_absolutelyContinuous _ _).map (measurable_pi_apply _)
  rw [p7_map_eval] at hac
  exact hac hs

theorem p7_core {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W)
    (hbdd : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∫⁻ x, f x ∂μ < ∞ →
      limsup (fun n => ∫⁻ ω, ∑ i : Fin n,
        ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop < ∞) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ C : ℝ≥0, 0 < C ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∀ n, n₀ ≤ n →
        ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ) ≤
          C * ∫⁻ x, f x ∂μ := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ k : ℕ, ∃ n, k + 1 ≤ n ∧ ∃ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A ∧
      (((4:ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) * μ A < p7nu μ W n A := by
    intro k
    obtain ⟨f, hf, n, hn, hlt⟩ := hcon (k + 1) (by omega) ((4:ℝ≥0) ^ k) (by positivity)
    refine ⟨n, hn, ?_⟩
    by_contra hA
    push_neg at hA
    have hle : p7nu μ W n ≤ (((4:ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) • μ := by
      rw [Measure.le_iff]
      intro s hs
      simpa using hA s hs
    have h2 := lintegral_mono' hle (le_refl (fun x => (f x : ℝ≥0∞)))
    rw [lintegral_smul_measure, p7nu_lintegral μ W hW n _ (by fun_prop)] at h2
    exact absurd hlt (not_lt.2 h2)
  choose n hn A hA hlt using key
  have hμpos : ∀ k, μ (A k) ≠ 0 := by
    intro k h0
    have h1 := p7nu_ac μ W (n k) h0
    have h2 := hlt k
    rw [h1] at h2
    exact (not_lt_zero h2)
  set c : ℕ → ℝ≥0∞ := fun k => ((2:ℝ≥0∞) ^ k)⁻¹ / μ (A k) with hc
  set F : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x => ∑' k, (A k).indicator (fun _ => c k) x with hF
  have hFm : Measurable F := Measurable.ennreal_tsum (fun k => measurable_const.indicator (hA k))
  have hFint : ∫⁻ x, F x ∂μ = ∑' k : ℕ, ((2:ℝ≥0∞) ^ k)⁻¹ := by
    rw [lintegral_tsum (fun k => (measurable_const.indicator (hA k)).aemeasurable)]
    congr 1; ext k
    rw [lintegral_indicator_const (hA k)]
    exact ENNReal.div_mul_cancel (hμpos k) (measure_ne_top _ _)
  have hFlt : ∫⁻ x, F x ∂μ < ∞ := by
    rw [hFint]
    simp_rw [ENNReal.inv_pow]
    rw [ENNReal.tsum_geometric]
    refine ENNReal.inv_lt_top.2 ?_
    exact tsub_pos_of_lt (ENNReal.inv_lt_one.2 (by norm_num))
  set f : EuclideanSpace ℝ (Fin d) → ℝ≥0 := fun x => (F x).toNNReal with hf
  have hfm : Measurable f := hFm.ennreal_toNNReal
  have hfi : ∫⁻ x, (f x : ℝ≥0∞) ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.coe_toNNReal_le_self)) hFlt
  have hae : ∀ m, ∀ᵐ x ∂(p7nu μ W m), (f x : ℝ≥0∞) = F x := by
    intro m
    have h0 : ∀ᵐ x ∂μ, F x < ∞ := ae_lt_top hFm hFlt.ne
    have h1 := (p7nu_ac μ W m).ae_le h0
    filter_upwards [h1] with x hx
    exact ENNReal.coe_toNNReal hx.ne
  have hbig : ∀ k, (2:ℝ≥0∞) ^ k ≤ ∫⁻ ω, ∑ i : Fin (n k),
      ENNReal.ofReal (wAt W (n k) ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ) := by
    intro k
    rw [← p7nu_lintegral μ W hW (n k) (fun x => (f x : ℝ≥0∞)) (by fun_prop),
      lintegral_congr_ae (hae (n k))]
    have e : c k * ((((4:ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) * μ (A k)) = (2:ℝ≥0∞) ^ k := by
      have h4 : (((4:ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) = (2:ℝ≥0∞) ^ k * (2:ℝ≥0∞) ^ k := by
        rw [← mul_pow]; push_cast; norm_num
      rw [hc, h4]
      simp only
      rw [ENNReal.div_eq_inv_mul]
      calc (μ (A k))⁻¹ * ((2:ℝ≥0∞) ^ k)⁻¹ * ((2:ℝ≥0∞) ^ k * (2:ℝ≥0∞) ^ k * μ (A k))
          = ((μ (A k))⁻¹ * μ (A k)) * ((((2:ℝ≥0∞) ^ k)⁻¹ * (2:ℝ≥0∞) ^ k) * (2:ℝ≥0∞) ^ k) := by ring
        _ = (2:ℝ≥0∞) ^ k := by
          rw [ENNReal.inv_mul_cancel (hμpos k) (measure_ne_top _ _),
            ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
          ring
    calc (2:ℝ≥0∞) ^ k = c k * ((((4:ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) * μ (A k)) := e.symm
      _ ≤ c k * p7nu μ W (n k) (A k) := by gcongr; exact (hlt k).le
      _ = ∫⁻ x, (A k).indicator (fun _ => c k) x ∂(p7nu μ W (n k)) :=
          (lintegral_indicator_const (hA k) _).symm
      _ ≤ ∫⁻ x, F x ∂(p7nu μ W (n k)) := lintegral_mono (fun x => ENNReal.le_tsum k)
  have hl := hbdd f hfm hfi
  set L := limsup (fun m => ∫⁻ ω, ∑ i : Fin m,
        ENNReal.ofReal (wAt W m ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop with hL
  have hge : L + 1 ≤ L := by
    refine le_limsup_of_frequently_le' ?_
    obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt (ENNReal.add_ne_top.2 ⟨hl.ne, ENNReal.one_ne_top⟩)
    rw [Filter.frequently_atTop]
    intro N
    refine ⟨n (N + K), by have := hn (N + K); omega, ?_⟩
    refine le_trans (le_of_lt hK) (le_trans ?_ (hbig (N + K)))
    have : (K : ℝ≥0∞) ≤ (2:ℝ≥0∞) ^ K := by
      exact_mod_cast (Nat.lt_two_pow_self).le
    exact this.trans (pow_le_pow_right₀ one_le_two (by omega))
  exact absurd hge (not_le.2 (ENNReal.lt_add_right hl.ne one_ne_zero))

end StoneRegression.Criterion

open StoneRegression.Criterion


theorem solution {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hnn : Nonneg W)
    (hbdd : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∫⁻ x, f x ∂μ < ∞ →
      limsup (fun n => ∫⁻ ω, ∑ i : Fin n,
        ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ)) atTop < ∞) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∃ C : ℝ≥0, 0 < C ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0, Measurable f → ∀ n, n₀ ≤ n →
        ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (wAt W n ω i) * (f (ω (i.val + 1)) : ℝ≥0∞) ∂(xLaw μ) ≤
          C * ∫⁻ x, f x ∂μ := by
  exact p7_core μ W hW hbdd
