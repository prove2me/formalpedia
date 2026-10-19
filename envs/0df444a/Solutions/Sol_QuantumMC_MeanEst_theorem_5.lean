-- Prove2me | solution 1 for QuantumMC.MeanEst.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T19:43:51.108552+00:00
-- url     : https://prove2.me/submissions/ff9ea555-ad20-4e05-a2e4-6f5cec9167ac

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting
import Theorems.Thm_QuantumMC_MeanEst_lemma_4_tail_bound
import Theorems.Thm_QuantumMC_MeanEst_lemma_4_decomposition
import Theorems.Thm_QuantumMC_MeanEst_lemma_4_cauchy_schwarz
import Theorems.Thm_QuantumMC_MeanEst_theorem_5_chebyshev
import Theorems.Thm_QuantumMC_MeanEst_theorem_5_l2_bound
import Theorems.Thm_QuantumMC_MeanEst_theorem_5_recombination

open MeasureTheory ProbabilityTheory Filter
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
open QuantumMC.MeanEst

private lemma integrable_truncIco {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : Integrable X P) (c d : ℝ) : Integrable (truncIco c d X) P := by
  have hXa : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
  refine Integrable.mono' hX.abs ?_ (Eventually.of_forall (fun ω => ?_))
  · refine (show AEMeasurable (truncIco c d X) P from
      ⟨truncIco c d (hXa.mk X), ?_, ?_⟩).aestronglyMeasurable
    · unfold truncIco
      exact Measurable.ite
        ((measurableSet_le measurable_const hXa.measurable_mk).inter
          (measurableSet_lt hXa.measurable_mk measurable_const))
        hXa.measurable_mk measurable_const
    · filter_upwards [hXa.ae_eq_mk] with ω hω
      simp only [truncIco, hω]
  · have hb : |truncIco c d X ω| ≤ |X ω| := by
      by_cases h : c ≤ X ω ∧ X ω < d
      · simp only [truncIco, if_pos h]; exact le_refl _
      · simp only [truncIco, if_neg h, abs_zero]; exact abs_nonneg _
    simpa only [Real.norm_eq_abs] using hb

private lemma integrable_truncGe {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : Integrable X P) (y : ℝ) : Integrable (truncGe y X) P := by
  have hXa : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
  refine Integrable.mono' hX.abs ?_ (Eventually.of_forall (fun ω => ?_))
  · refine (show AEMeasurable (truncGe y X) P from
      ⟨truncGe y (hXa.mk X), ?_, ?_⟩).aestronglyMeasurable
    · unfold truncGe
      exact Measurable.ite (measurableSet_le measurable_const hXa.measurable_mk)
        hXa.measurable_mk measurable_const
    · filter_upwards [hXa.ae_eq_mk] with ω hω
      simp only [truncGe, hω]
  · have hb : |truncGe y X ω| ≤ |X ω| := by
      by_cases h : y ≤ X ω
      · simp only [truncGe, if_pos h]; exact le_refl _
      · simp only [truncGe, if_neg h, abs_zero]; exact abs_nonneg _
    simpa only [Real.norm_eq_abs] using hb

/-- **Lemma 4 accuracy part** (Montanaro arXiv:1504.06987v3, §2.2, pp. 10–11).

If every Algorithm 1 call made by Algorithm 2 returns a value satisfying
Theorem 3's accuracy bound (`Alg2Succeeds`), then the dyadic estimator
`alg2Output (alg2K ε) μ` approximates `∫ X` up to additive error
`ε (‖X‖₂ + 1)²`, provided the universal constant `D` is large enough
(`4C ≤ D` and `20C ≤ D²`). -/
private lemma alg2_error_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C D ε : ℝ) (X : Ω → ℝ) (μ : ℕ → ℝ)
    (hC : 0 < C) (hD1 : 4 * C ≤ D) (hD2 : 20 * C ≤ D ^ 2)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hX : MemLp X 2 P) (hpos : ∀ ω, 0 ≤ X ω)
    (hS : Alg2Succeeds C D ε P X μ) :
    |alg2Output (alg2K ε) μ - (∫ ω, X ω ∂P)| ≤ ε * (l2norm P X + 1) ^ 2 := by
  have hIntX : Integrable X P := hX.integrable (by norm_num)
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hεle1 : ε ≤ 1 := by linarith
  have hinvpos : 0 < 1 / ε := by positivity
  have hinv1 : 1 < 1 / ε := by rw [one_lt_div hε0]; linarith
  set L : ℝ := Real.logb 2 (1 / ε) with hL
  have hLpos : 0 < L := by rw [hL]; exact Real.logb_pos (by norm_num) hinv1
  have hLge1 : 1 ≤ L := by
    rw [hL, Real.le_logb_iff_rpow_le (by norm_num) hinvpos, Real.rpow_one, le_div_iff₀ hε0]
    linarith
  set k : ℕ := alg2K ε with hk
  set t : ℕ := alg2T D ε with ht
  have hk_ge : L ≤ (k : ℝ) := by
    rw [hk]; unfold alg2K; rw [← hL]; exact Nat.le_ceil _
  have hk_le : (k : ℝ) ≤ L + 1 := by
    have h : (k : ℝ) < L + 1 := by
      rw [hk]; unfold alg2K; rw [← hL]
      exact Nat.ceil_lt_add_one (le_of_lt hLpos)
    linarith
  have hpowL : (2 : ℝ) ^ L = 1 / ε := by
    rw [hL]; exact Real.rpow_logb (by norm_num) (by norm_num) hinvpos
  have hpow_ge : 1 / ε ≤ (2 : ℝ) ^ k := by
    have h1 : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ (k : ℝ) :=
      (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hk_ge
    rw [Real.rpow_natCast, hpowL] at h1
    exact h1
  have hpow_le : (2 : ℝ) ^ k ≤ 2 / ε := by
    have h1 : (2 : ℝ) ^ (k : ℝ) ≤ (2 : ℝ) ^ (L + 1) :=
      (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hk_le
    have h2 : (2 : ℝ) ^ (L + 1) = 2 / ε := by
      rw [Real.rpow_add (by norm_num), hpowL, Real.rpow_one]; ring
    rw [Real.rpow_natCast, h2] at h1
    exact h1
  have hDpos : 0 < D := by linarith
  have hsqrtLpos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hDLpos : 0 < D * Real.sqrt L := by positivity
  have ht_ge : D * Real.sqrt L / ε ≤ (t : ℝ) := by
    rw [ht]; unfold alg2T; rw [← hL]; exact Nat.le_ceil _
  have ht_pos : 0 < (t : ℝ) := lt_of_lt_of_le (by positivity) ht_ge
  -- ### integrability and nonnegativity helpers
  have htrI_nn : ∀ c d ω, 0 ≤ truncIco c d X ω := by
    intro c d ω
    by_cases h : c ≤ X ω ∧ X ω < d
    · simp only [truncIco, if_pos h]; exact hpos ω
    · simp only [truncIco, if_neg h]; exact le_refl 0
  have htrG_nn : ∀ y ω, 0 ≤ truncGe y X ω := by
    intro y ω
    by_cases h : y ≤ X ω
    · simp only [truncGe, if_pos h]; exact hpos ω
    · simp only [truncGe, if_neg h]; exact le_refl 0
  -- ### named components
  set E0 : ℝ := ∫ ω, truncIco 0 1 X ω ∂P with hE0
  set EE : ℕ → ℝ := fun ℓ => ∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P with hEE
  set b : ℕ → ℝ := fun ℓ => ∫ ω, band X ℓ ω ∂P with hb
  set tl : ℝ := ∫ ω, truncGe ((2 : ℝ) ^ k) X ω ∂P with htl
  set S : ℝ := ∑ ℓ ∈ Finset.Icc 1 k, Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt (EE ℓ) with hSd
  set T2 : ℝ := ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ with hT2d
  set l : ℝ := l2norm P X with hl
  set Af : ℝ := alg2Output k μ with hAf
  have hl_nn : 0 ≤ l := by rw [hl]; exact Real.sqrt_nonneg _
  have hEE_nn : ∀ ℓ, 0 ≤ EE ℓ :=
    fun ℓ => integral_nonneg (fun ω => htrI_nn _ _ ω)
  have hb_nn : ∀ ℓ, 0 ≤ b ℓ :=
    fun ℓ => integral_nonneg (fun ω => div_nonneg (htrI_nn _ _ ω) (by positivity))
  have htl_nn : 0 ≤ tl := integral_nonneg (fun ω => htrG_nn _ ω)
  have hE0_le : E0 ≤ 1 := by
    have hle : ∀ ω, truncIco 0 1 X ω ≤ 1 := by
      intro ω
      by_cases h : (0 : ℝ) ≤ X ω ∧ X ω < 1
      · simp only [truncIco, if_pos h]; exact le_of_lt h.2
      · simp only [truncIco, if_neg h]; norm_num
    calc E0 = ∫ ω, truncIco 0 1 X ω ∂P := rfl
      _ ≤ ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_mono (integrable_truncIco P X hIntX 0 1) (integrable_const 1) hle
      _ = 1 := by simp
  -- ### band averages in terms of the interval integrals
  have hbE : ∀ ℓ, (2 : ℝ) ^ ℓ * b ℓ = EE ℓ := by
    intro ℓ
    have hb' : b ℓ = ((2 : ℝ) ^ ℓ)⁻¹ * EE ℓ := by
      show (∫ ω, band X ℓ ω ∂P) =
        ((2 : ℝ) ^ ℓ)⁻¹ * (∫ ω, truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω ∂P)
      rw [show band X ℓ =
          (fun ω => ((2 : ℝ) ^ ℓ)⁻¹ *
            truncIco ((2 : ℝ) ^ (ℓ - 1)) ((2 : ℝ) ^ ℓ) X ω) from by
        funext ω; simp only [band, div_eq_mul_inv]; ring]
      rw [integral_const_mul]
    rw [hb', ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero ℓ (by norm_num)), one_mul]
  -- ### per-band Algorithm-1 error
  obtain ⟨hS1raw, hS2raw⟩ := hS
  have hS2' : ∀ ℓ ∈ Finset.Icc 1 k,
      |μ ℓ - b ℓ| ≤ C * (Real.sqrt (b ℓ) / (t : ℝ) + 1 / (t : ℝ) ^ 2) := by
    intro ℓ hℓ
    have hℓ' : ℓ ∈ Finset.Icc 1 (alg2K ε) := by rwa [← hk]
    exact hS2raw ℓ hℓ'
  have hper : ∀ ℓ ∈ Finset.Icc 1 k,
      (2 : ℝ) ^ ℓ * |μ ℓ - b ℓ| ≤
        C / t * (Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt (EE ℓ)) + C / t ^ 2 * (2 : ℝ) ^ ℓ := by
    intro ℓ hℓ
    have h1 : |μ ℓ - b ℓ| ≤ C * (Real.sqrt (b ℓ) / (t : ℝ) + 1 / (t : ℝ) ^ 2) := hS2' ℓ hℓ
    have hsqrt2 : Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt ((2 : ℝ) ^ ℓ) = (2 : ℝ) ^ ℓ := by
      rw [← sq, Real.sq_sqrt (by positivity)]
    have hsq : Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt (EE ℓ) = (2 : ℝ) ^ ℓ * Real.sqrt (b ℓ) := by
      have hEEeq : EE ℓ = (2 : ℝ) ^ ℓ * b ℓ := (hbE ℓ).symm
      rw [hEEeq, Real.sqrt_mul (by positivity)]
      rw [← mul_assoc, hsqrt2]
    calc (2 : ℝ) ^ ℓ * |μ ℓ - b ℓ|
        ≤ (2 : ℝ) ^ ℓ * (C * (Real.sqrt (b ℓ) / (t : ℝ) + 1 / (t : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C / t * (Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt (EE ℓ))
            + C / t ^ 2 * (2 : ℝ) ^ ℓ := by
          rw [hsq]; ring
  have hsum_le : ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * |μ ℓ - b ℓ| ≤
      C / t * S + C / t ^ 2 * T2 := by
    calc ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * |μ ℓ - b ℓ|
        ≤ ∑ ℓ ∈ Finset.Icc 1 k,
            (C / t * (Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt (EE ℓ))
              + C / t ^ 2 * (2 : ℝ) ^ ℓ) := Finset.sum_le_sum hper
      _ = C / t * (∑ ℓ ∈ Finset.Icc 1 k, Real.sqrt ((2 : ℝ) ^ ℓ) * Real.sqrt (EE ℓ))
            + C / t ^ 2 * (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = C / t * S + C / t ^ 2 * T2 := rfl
  have habs_sum : |∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (μ ℓ - b ℓ)| ≤
      ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * |μ ℓ - b ℓ| := by
    refine (Finset.abs_sum_le_sum_abs
      (fun ℓ => (2 : ℝ) ^ ℓ * (μ ℓ - b ℓ)) (Finset.Icc 1 k)).trans ?_
    exact Finset.sum_le_sum (fun ℓ _ => by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ℓ)])
  have hAsum : (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * μ ℓ)
        - (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * b ℓ)
      = ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (μ ℓ - b ℓ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun ℓ _ => by ring)
  have hAunfold : Af = μ 0 + ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * μ ℓ := rfl
  have hdec' : (∫ ω, X ω ∂P) = E0 + (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * b ℓ) + tl :=
    QuantumMC.MeanEst.lemma_4_decomposition P X hIntX hpos k
  have hkey1 : Af - (∫ ω, X ω ∂P)
      = (μ 0 - E0) + (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (μ ℓ - b ℓ)) - tl := by
    rw [hAunfold, hdec']
    rw [show (μ 0 + ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * μ ℓ)
          - (E0 + (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * b ℓ) + tl)
        = (μ 0 - E0)
          + ((∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * μ ℓ)
             - (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * b ℓ)) - tl from by ring]
    rw [hAsum]
  have htri : |Af - (∫ ω, X ω ∂P)| ≤
      |μ 0 - E0| + (C / t * S + C / t ^ 2 * T2) + tl := by
    calc |Af - (∫ ω, X ω ∂P)|
        = |(μ 0 - E0)
            + (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (μ ℓ - b ℓ)) - tl| := by rw [hkey1]
      _ ≤ |(μ 0 - E0)
            + (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (μ ℓ - b ℓ))| + |tl| := abs_sub _ _
      _ ≤ (|μ 0 - E0| + ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * |μ ℓ - b ℓ|) + tl := by
            rw [abs_of_nonneg htl_nn]
            linarith [abs_add_le (μ 0 - E0)
              (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ * (μ ℓ - b ℓ)), habs_sum]
      _ ≤ (|μ 0 - E0| + (C / t * S + C / t ^ 2 * T2)) + tl := by linarith [hsum_le]
  have h0 : |μ 0 - E0| ≤ C / t + C / t ^ 2 := by
    have hS1 : |μ 0 - (∫ ω, truncIco 0 1 X ω ∂P)| ≤
        C * (Real.sqrt (∫ ω, truncIco 0 1 X ω ∂P) / (t : ℝ) + 1 / (t : ℝ) ^ 2) := hS1raw
    have hsqrt : Real.sqrt (∫ ω, truncIco 0 1 X ω ∂P) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hE0_le
    have hdiv : Real.sqrt (∫ ω, truncIco 0 1 X ω ∂P) / (t : ℝ) ≤ 1 / (t : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hsqrt (by positivity)
    calc |μ 0 - E0|
        ≤ C * (Real.sqrt (∫ ω, truncIco 0 1 X ω ∂P) / (t : ℝ) + 1 / (t : ℝ) ^ 2) := hS1
      _ ≤ C * (1 / (t : ℝ) + 1 / (t : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
            linarith [hdiv]
      _ = C / t + C / t ^ 2 := by ring
  have hS_le : S ≤ Real.sqrt (2 * (k : ℝ)) * l :=
    (QuantumMC.MeanEst.lemma_4_cauchy_schwarz P X hX hpos k).1.trans
      (QuantumMC.MeanEst.lemma_4_cauchy_schwarz P X hX hpos k).2
  have htail : tl ≤ l ^ 2 / (2 : ℝ) ^ k :=
    QuantumMC.MeanEst.lemma_4_tail_bound P X hX hpos k
  have hCS : C / t * S ≤ C / t * (Real.sqrt (2 * (k : ℝ)) * l) :=
    mul_le_mul_of_nonneg_left hS_le (by positivity)
  have hmain : |Af - (∫ ω, X ω ∂P)|
      ≤ C / t * (1 + Real.sqrt (2 * (k : ℝ)) * l) + C / t ^ 2 * (1 + T2)
        + l ^ 2 / (2 : ℝ) ^ k := by
    calc |Af - (∫ ω, X ω ∂P)| ≤ |μ 0 - E0| + (C / t * S + C / t ^ 2 * T2) + tl := htri
      _ ≤ (C / t + C / t ^ 2) + (C / t * S + C / t ^ 2 * T2) + l ^ 2 / (2 : ℝ) ^ k := by
            linarith [h0, htail]
      _ ≤ C / t * (1 + Real.sqrt (2 * (k : ℝ)) * l) + C / t ^ 2 * (1 + T2)
            + l ^ 2 / (2 : ℝ) ^ k := by linarith [hCS]
  -- ### numeric comparison
  have hCD : C / D ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hDpos (by norm_num : (0 : ℝ) < 4)]; linarith [hD1]
  have hCD2 : C / D ^ 2 ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < D ^ 2) (by norm_num : (0 : ℝ) < 20)]
    linarith [hD2]
  have hrec1 : 1 / (t : ℝ) ≤ ε / (D * Real.sqrt L) := by
    rw [div_le_div_iff₀ ht_pos hDLpos]
    have h1 : D * Real.sqrt L ≤ (t : ℝ) * ε := by
      have := (div_le_iff₀ hε0).mp ht_ge
      linarith [this]
    linarith [h1]
  have hrec2 : 1 / (t : ℝ) ^ 2 ≤ ε ^ 2 / (D ^ 2 * L) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (t : ℝ) ^ 2)
      (by positivity : (0 : ℝ) < D ^ 2 * L)]
    have h2 : (D * Real.sqrt L / ε) ^ 2 ≤ (t : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) ht_ge 2
    have h3 : (D * Real.sqrt L / ε) ^ 2 = D ^ 2 * L / ε ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hLpos)]
    rw [h3] at h2
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)] at h2
    nlinarith [h2]
  have hct1 : C / (t : ℝ) ≤ ε / 4 := by
    have h1 : C / (t : ℝ) ≤ C * (ε / (D * Real.sqrt L)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hrec1 (le_of_lt hC)
    have hsq : ε / Real.sqrt L ≤ ε := by
      rw [div_le_iff₀ hsqrtLpos]
      calc ε = ε * 1 := by ring
        _ ≤ ε * Real.sqrt L :=
            mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hLge1) (le_of_lt hε0)
    calc C / (t : ℝ) ≤ C * (ε / (D * Real.sqrt L)) := h1
      _ = (C / D) * (ε / Real.sqrt L) := by ring
      _ ≤ (1 / 4) * ε := mul_le_mul hCD hsq (by positivity) (by norm_num)
      _ = ε / 4 := by ring
  have hct2 : C / (t : ℝ) ^ 2 ≤ ε / 20 := by
    have h1 : C / (t : ℝ) ^ 2 ≤ C * (ε ^ 2 / (D ^ 2 * L)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hrec2 (le_of_lt hC)
    have hεL : ε ^ 2 / L ≤ ε := by
      rw [div_le_iff₀ hLpos]; nlinarith [hεle1, hLge1, hε0]
    calc C / (t : ℝ) ^ 2 ≤ C * (ε ^ 2 / (D ^ 2 * L)) := h1
      _ = (C / D ^ 2) * (ε ^ 2 / L) := by ring
      _ ≤ (1 / 20) * ε := mul_le_mul hCD2 hεL (by positivity) (by norm_num)
      _ = ε / 20 := by ring
  have hs2 : Real.sqrt (2 * (k : ℝ)) ≤ 2 * Real.sqrt L := by
    have h4 : Real.sqrt (4 * L) = 2 * Real.sqrt L := by
      rw [show (4 : ℝ) * L = 2 ^ 2 * L by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← h4]
    apply Real.sqrt_le_sqrt
    nlinarith [hk_le, hLge1]
  have hT2b : T2 ≤ (L + 1) * (2 / ε) := by
    have h1 : T2 ≤ (2 : ℝ) ^ k * (k : ℝ) := by
      show (∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ) ≤ (2 : ℝ) ^ k * (k : ℝ)
      calc ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ ℓ ≤ ∑ ℓ ∈ Finset.Icc 1 k, (2 : ℝ) ^ k :=
            Finset.sum_le_sum (fun ℓ hℓ => pow_le_pow_right₀ (by norm_num) (Finset.mem_Icc.mp hℓ).2)
        _ = (2 : ℝ) ^ k * (k : ℝ) := by
            rw [Finset.sum_const, Nat.card_Icc]; simp [nsmul_eq_mul, mul_comm]
    calc T2 ≤ (2 : ℝ) ^ k * (k : ℝ) := h1
      _ ≤ (2 / ε) * (L + 1) := mul_le_mul hpow_le hk_le (by positivity) (by positivity)
      _ = (L + 1) * (2 / ε) := by ring
  have hprod1 : C / (t : ℝ) * (Real.sqrt (2 * (k : ℝ)) * l) ≤ 2 * C * ε * l / D := by
    have h3 : Real.sqrt (2 * (k : ℝ)) * l ≤ 2 * Real.sqrt L * l :=
      mul_le_mul_of_nonneg_right hs2 hl_nn
    have hct' : C / (t : ℝ) ≤ C * ε / (D * Real.sqrt L) := by
      have h1 : C / (t : ℝ) ≤ C * (ε / (D * Real.sqrt L)) := by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hrec1 (le_of_lt hC)
      calc C / (t : ℝ) ≤ C * (ε / (D * Real.sqrt L)) := h1
        _ = C * ε / (D * Real.sqrt L) := by ring
    calc C / (t : ℝ) * (Real.sqrt (2 * (k : ℝ)) * l)
        ≤ (C * ε / (D * Real.sqrt L)) * (2 * Real.sqrt L * l) :=
          mul_le_mul hct' h3 (by positivity) (by positivity)
      _ = 2 * C * ε * l / D := by field_simp
  have hprod2 : C / (t : ℝ) ^ 2 * T2 ≤ 4 * C * ε / D ^ 2 := by
    have hct2' : C / (t : ℝ) ^ 2 ≤ C * ε ^ 2 / (D ^ 2 * L) := by
      have h1 : C / (t : ℝ) ^ 2 ≤ C * (ε ^ 2 / (D ^ 2 * L)) := by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hrec2 (le_of_lt hC)
      calc C / (t : ℝ) ^ 2 ≤ C * (ε ^ 2 / (D ^ 2 * L)) := h1
        _ = C * ε ^ 2 / (D ^ 2 * L) := by ring
    have h1 := mul_le_mul hct2' hT2b (by positivity) (by positivity)
    have hLL : (L + 1) / L ≤ 2 := by rw [div_le_iff₀ hLpos]; linarith
    calc C / (t : ℝ) ^ 2 * T2
        ≤ (C * ε ^ 2 / (D ^ 2 * L)) * ((L + 1) * (2 / ε)) := h1
      _ = 2 * C * ε * (L + 1) / (D ^ 2 * L) := by field_simp
      _ ≤ 4 * C * ε / D ^ 2 := by
            have hfac : 2 * C * ε * (L + 1) / (D ^ 2 * L)
                = (2 * C * ε / D ^ 2) * ((L + 1) / L) := by ring
            rw [hfac]
            calc (2 * C * ε / D ^ 2) * ((L + 1) / L) ≤ (2 * C * ε / D ^ 2) * 2 :=
                  mul_le_mul_of_nonneg_left hLL (by positivity)
              _ = 4 * C * ε / D ^ 2 := by ring
  have hdiv3 : l ^ 2 / (2 : ℝ) ^ k ≤ ε * l ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
    have h2k : 1 ≤ ε * (2 : ℝ) ^ k := by
      have h := hpow_ge
      rw [div_le_iff₀ hε0] at h
      linarith [h]
    nlinarith [sq_nonneg l, h2k]
  have hB : 2 * C * ε * l / D ≤ ε * l / 2 := by
    have he : 2 * C * ε * l / D = (C / D) * (2 * ε * l) := by ring
    rw [he]
    calc (C / D) * (2 * ε * l) ≤ (1 / 4) * (2 * ε * l) :=
          mul_le_mul_of_nonneg_right hCD (by positivity)
      _ = ε * l / 2 := by ring
  have hD_ : 4 * C * ε / D ^ 2 ≤ ε / 5 := by
    have he : 4 * C * ε / D ^ 2 = 4 * ε * (C / D ^ 2) := by ring
    rw [he]
    calc 4 * ε * (C / D ^ 2) ≤ 4 * ε * (1 / 20) :=
          mul_le_mul_of_nonneg_left hCD2 (by positivity)
      _ = ε / 5 := by ring
  have hterm1 : C / (t : ℝ) * (1 + Real.sqrt (2 * (k : ℝ)) * l) ≤ ε / 4 + ε * l / 2 := by
    have he : C / (t : ℝ) * (1 + Real.sqrt (2 * (k : ℝ)) * l)
        = C / t + C / t * (Real.sqrt (2 * (k : ℝ)) * l) := by ring
    rw [he]; linarith [hct1, hprod1, hB]
  have hterm2 : C / (t : ℝ) ^ 2 * (1 + T2) ≤ ε / 4 := by
    have he : C / (t : ℝ) ^ 2 * (1 + T2) = C / t ^ 2 + C / t ^ 2 * T2 := by ring
    rw [he]; linarith [hct2, hprod2, hD_]
  have hnum : C / t * (1 + Real.sqrt (2 * (k : ℝ)) * l) + C / t ^ 2 * (1 + T2)
      + l ^ 2 / (2 : ℝ) ^ k ≤ ε * (l + 1) ^ 2 := by
    have h2 : ε / 4 + ε * l / 2 + ε / 4 + ε * l ^ 2 ≤ ε * (l + 1) ^ 2 := by
      nlinarith [hl_nn, hε0]
    linarith [hterm1, hterm2, hdiv3, h2]
  calc |Af - (∫ ω, X ω ∂P)|
      ≤ C / t * (1 + Real.sqrt (2 * (k : ℝ)) * l) + C / t ^ 2 * (1 + T2)
        + l ^ 2 / (2 : ℝ) ^ k := hmain
    _ ≤ ε * (l + 1) ^ 2 := hnum
    _ = ε * (l2norm P X + 1) ^ 2 := by rw [hl]
/-- `alg3B σ m X` is in `L²` whenever `X` is. -/
private lemma memLp_alg3B {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (σ m : ℝ) (hX : MemLp X 2 P) :
    MemLp (alg3B σ m X) 2 P := by
  change MemLp (fun x => X x / σ - m) 2 P
  have h1 : MemLp (fun x => X x / σ) 2 P := by
    have h := hX.const_mul (σ⁻¹)
    convert h using 1
    ext x; rw [div_eq_mul_inv, mul_comm]
  exact h1.sub (memLp_const m)

/-- Pointwise-domination comparison for `l2norm`. -/
private lemma l2norm_le_of_abs_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f g : Ω → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (h : ∀ ω, |f ω| ≤ |g ω|) : l2norm P f ≤ l2norm P g := by
  unfold l2norm
  apply Real.sqrt_le_sqrt
  refine integral_mono hf.integrable_sq hg.integrable_sq (fun ω => ?_)
  have := pow_le_pow_left₀ (abs_nonneg (f ω)) (h ω) 2
  simpa only [sq_abs] using this

/-- `l2norm` rescales by `1/4`. -/
private lemma l2norm_div_four {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → ℝ) (hB : MemLp B 2 P) :
    l2norm P (fun ω => B ω / 4) = l2norm P B / 4 := by
  unfold l2norm
  rw [show (∫ ω, (B ω / 4) ^ 2 ∂P) = (1 / 16) * ∫ ω, B ω ^ 2 ∂P from by
        rw [show (fun ω => (B ω / 4) ^ 2) = (fun ω => (1 / 16) * B ω ^ 2) from by
              funext ω; ring]
        rw [integral_const_mul]]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 16),
      show Real.sqrt (1 / 16) = (1 / 4 : ℝ) from by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

private lemma abs_four : |(4 : ℝ)| = 4 := abs_of_nonneg (by norm_num)

private lemma abs_div_four (x : ℝ) : |x / 4| = |x| / 4 := by
  rw [abs_div, abs_four]

private lemma abs_div_four_le {x y : ℝ} (h : |x| ≤ |y|) : |x / 4| ≤ |y / 4| := by
  have hx : |x / 4| = |x| / 4 := abs_div_four x
  have hy : |y / 4| = |y| / 4 := abs_div_four y
  rw [hx, hy]
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- The two quarter functions of `B` are in `L²` when `B` is. -/
private lemma memLp_alg3_quarters {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → ℝ) (hmB : Measurable B) (hB : MemLp B 2 P) :
    MemLp (fun ω => truncGe 0 B ω / 4) 2 P ∧
      MemLp (fun ω => -(truncLt 0 B ω) / 4) 2 P := by
  have hg : MemLp (fun ω => B ω / 4) 2 P := by
    have h := hB.const_mul ((4 : ℝ)⁻¹)
    convert h using 1
    ext ω; rw [div_eq_mul_inv, mul_comm]
  have hG : ∀ ω, |truncGe 0 B ω / 4| ≤ |B ω / 4| := by
    intro ω
    have hnn : 0 ≤ truncGe 0 B ω := by
      unfold truncGe; split_ifs with h
      · exact h
      · exact le_refl 0
    have hle : truncGe 0 B ω ≤ |B ω| := by
      unfold truncGe; split_ifs with h
      · rw [abs_of_nonneg h]
      · exact abs_nonneg _
    exact abs_div_four_le (by rwa [abs_of_nonneg hnn])
  have hL : ∀ ω, |-(truncLt 0 B ω) / 4| ≤ |B ω / 4| := by
    intro ω
    have hle : |truncLt 0 B ω| ≤ |B ω| := by
      unfold truncLt; split_ifs with h
      · rw [abs_of_neg h]
      · rw [abs_zero]; exact abs_nonneg _
    exact abs_div_four_le (x := -(truncLt 0 B ω)) (by rwa [abs_neg])
  exact ⟨MemLp.of_le hg ((Measurable.ite (measurableSet_le measurable_const hmB) hmB
      measurable_const : Measurable (truncGe 0 B)).div_const 4).aestronglyMeasurable
      (Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs] using hG ω)),
    MemLp.of_le hg (((Measurable.ite (measurableSet_lt hmB measurable_const) hmB
      measurable_const).neg).div_const 4).aestronglyMeasurable
      (Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs] using hL ω))⟩

/-- If `‖B‖₂ ≤ 4` then each quarter of `B` has `‖·‖₂ ≤ 1`. -/
private lemma l2norm_quarter_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → ℝ) (hmB : Measurable B) (hB : MemLp B 2 P)
    (hl : l2norm P B ≤ 4) :
    l2norm P (fun ω => truncGe 0 B ω / 4) ≤ 1 ∧
      l2norm P (fun ω => -(truncLt 0 B ω) / 4) ≤ 1 := by
  have hmem := memLp_alg3_quarters P B hmB hB
  have hg : MemLp (fun ω => B ω / 4) 2 P := by
    have h := hB.const_mul ((4 : ℝ)⁻¹)
    convert h using 1
    ext ω; rw [div_eq_mul_inv, mul_comm]
  have hG : ∀ ω, |truncGe 0 B ω / 4| ≤ |B ω / 4| := by
    intro ω
    have hnn : 0 ≤ truncGe 0 B ω := by
      unfold truncGe; split_ifs with h
      · exact h
      · exact le_refl 0
    have hle : truncGe 0 B ω ≤ |B ω| := by
      unfold truncGe; split_ifs with h
      · rw [abs_of_nonneg h]
      · exact abs_nonneg _
    exact abs_div_four_le (by rwa [abs_of_nonneg hnn])
  have hL : ∀ ω, |-(truncLt 0 B ω) / 4| ≤ |B ω / 4| := by
    intro ω
    have hle : |truncLt 0 B ω| ≤ |B ω| := by
      unfold truncLt; split_ifs with h
      · rw [abs_of_neg h]
      · rw [abs_zero]; exact abs_nonneg _
    exact abs_div_four_le (x := -(truncLt 0 B ω)) (by rwa [abs_neg])
  constructor
  · have hle := l2norm_le_of_abs_le P _ _ hmem.1 hg hG
    rw [l2norm_div_four P B hB] at hle
    calc l2norm P (fun ω => truncGe 0 B ω / 4) ≤ l2norm P B / 4 := hle
      _ ≤ 4 / 4 := div_le_div_of_nonneg_right hl (by norm_num)
      _ = 1 := by norm_num
  · have hle := l2norm_le_of_abs_le P _ _ hmem.2 hg hL
    rw [l2norm_div_four P B hB] at hle
    calc l2norm P (fun ω => -(truncLt 0 B ω) / 4) ≤ l2norm P B / 4 := hle
      _ ≤ 4 / 4 := div_le_div_of_nonneg_right hl (by norm_num)
      _ = 1 := by norm_num

/-- `MemLp` for the negative/positive quarters of `alg3B`. -/
private lemma alg3_quarters_memLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (σ m : ℝ) (hB : MemLp (alg3B σ m X) 2 P) (hmB : Measurable (alg3B σ m X)) :
    MemLp (alg3NegQuarter σ m X) 2 P ∧ MemLp (alg3PosQuarter σ m X) 2 P := by
  have h := memLp_alg3_quarters P (alg3B σ m X) hmB hB
  exact ⟨by unfold alg3NegQuarter; exact h.2,
    by unfold alg3PosQuarter; exact h.1⟩

/-- `l2norm ≤ 1` for the negative/positive quarters of `alg3B`. -/
private lemma alg3_quarters_l2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (σ m : ℝ) (hB : MemLp (alg3B σ m X) 2 P)
    (hmB : Measurable (alg3B σ m X)) (hl : l2norm P (alg3B σ m X) ≤ 4) :
    l2norm P (alg3NegQuarter σ m X) ≤ 1 ∧ l2norm P (alg3PosQuarter σ m X) ≤ 1 := by
  have h := l2norm_quarter_le P (alg3B σ m X) hmB hB hl
  exact ⟨by unfold alg3NegQuarter; exact h.2,
    by unfold alg3PosQuarter; exact h.1⟩

universe u v

/-- Theorem 5, p. 12: Algorithm 3 has additive error ε with probability at least 2/3. -/
theorem solution (C : ℝ) (hC : 0 < C) : ∃ D : ℝ, 0 < D ∧
    ∀ (Ω₀ : Type u) [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
      (X : Ω₀ → ℝ) (σ ε : ℝ), Measurable X → MemLp X 2 P₀ →
      variance X P₀ ≤ σ ^ 2 → 0 < σ → 0 < ε → ε < 4 * σ →
    ∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m : Ω → ℝ) (μneg μpos : Ω → ℕ → ℝ),
      Measurable m → P.map m = P₀.map (fun x => X x / σ) →
      P {ω | ¬ Alg2Succeeds C D (ε / (32 * σ)) P₀
        (alg3NegQuarter σ (m ω) X) (μneg ω)} ≤ (1 / 9 : ENNReal) →
      P {ω | ¬ Alg2Succeeds C D (ε / (32 * σ)) P₀
        (alg3PosQuarter σ (m ω) X) (μpos ω)} ≤ (1 / 9 : ENNReal) →
      (2 / 3 : ENNReal) ≤ P {ω |
        |alg3Output σ (m ω) (alg2K (ε / (32 * σ)))
          (μneg ω) (μpos ω) - ∫ x, X x ∂P₀| ≤ ε} := by
  classical
  set D : ℝ := max (4 * C) (max 1 (Real.sqrt (20 * C))) with hD
  have hDpos : 0 < D := by
    rw [hD]
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) < 4 * C) (le_max_left _ _)
  have hD1 : 4 * C ≤ D := by rw [hD]; exact le_max_left _ _
  have hD2 : 20 * C ≤ D ^ 2 := by
    rw [hD]
    have hle : Real.sqrt (20 * C) ≤ max (4 * C) (max 1 (Real.sqrt (20 * C))) :=
      le_trans (le_max_right 1 (Real.sqrt (20 * C))) (le_max_right (4 * C) _)
    have hnn : 0 ≤ Real.sqrt (20 * C) := Real.sqrt_nonneg _
    have hsq : (Real.sqrt (20 * C)) ^ 2 = 20 * C := Real.sq_sqrt (by positivity)
    calc 20 * C = (Real.sqrt (20 * C)) ^ 2 := hsq.symm
      _ ≤ (max (4 * C) (max 1 (Real.sqrt (20 * C)))) ^ 2 := pow_le_pow_left₀ hnn hle 2
  refine ⟨D, hDpos, ?_⟩
  intro Ω₀ instΩ₀ P₀ instP₀ X σ ε hXm hXmem hvar hσ0 hε0 hεlt Ω instΩ P instP m μneg μpos
    hm hmap hfailNeg hfailPos
  set c : ℝ := ∫ x, X x / σ ∂P₀ with hc
  set ε' : ℝ := ε / (32 * σ) with hε'
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  have h32σ : 0 < 32 * σ := by positivity
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hε'1 : ε' ≤ 1 / 2 := by
    rw [hε', div_le_iff₀ h32σ]
    linarith [hεlt, hσ0]
  set E : Set Ω := {ω | |m ω - c| ≤ 3} with hE
  set N : Set Ω := {ω | ¬ Alg2Succeeds C D ε' P₀ (alg3NegQuarter σ (m ω) X) (μneg ω)} with hN
  set Pset : Set Ω := {ω | ¬ Alg2Succeeds C D ε' P₀ (alg3PosQuarter σ (m ω) X) (μpos ω)} with hPset
  set Final : Set Ω :=
    {ω | |alg3Output σ (m ω) (alg2K ε') (μneg ω) (μpos ω) - ∫ x, X x ∂P₀| ≤ ε} with hFinal
  have hgood : E ∩ Nᶜ ∩ Psetᶜ ⊆ Final := by
    intro ω hω
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, hE, hN, hPset, Set.mem_setOf_eq, not_not]
      at hω
    obtain ⟨⟨hEω, hNω⟩, hPω⟩ := hω
    simp only [hFinal, Set.mem_setOf_eq]
    have hBmem : MemLp (alg3B σ (m ω) X) 2 P₀ := memLp_alg3B P₀ X σ (m ω) hXmem
    have hBmeas : Measurable (alg3B σ (m ω) X) := (hXm.div_const σ).sub measurable_const
    have hl2B : l2norm P₀ (alg3B σ (m ω) X) ≤ 4 :=
      theorem_5_l2_bound P₀ X hXm hXmem σ hvar hσ0 (m ω) hEω
    have hqmem := alg3_quarters_memLp P₀ X σ (m ω) hBmem hBmeas
    have hql2 := alg3_quarters_l2 P₀ X σ (m ω) hBmem hBmeas hl2B
    have hnnNeg : ∀ x, 0 ≤ alg3NegQuarter σ (m ω) X x := by
      intro x
      unfold alg3NegQuarter
      have h : truncLt 0 (alg3B σ (m ω) X) x ≤ 0 := by
        unfold truncLt; split_ifs with hh
        · linarith
        · exact le_refl 0
      exact div_nonneg (by linarith) (by norm_num)
    have hnnPos : ∀ x, 0 ≤ alg3PosQuarter σ (m ω) X x := by
      intro x
      unfold alg3PosQuarter
      have h : 0 ≤ truncGe 0 (alg3B σ (m ω) X) x := by
        unfold truncGe; split_ifs with hh
        · exact hh
        · exact le_refl 0
      exact div_nonneg h (by norm_num)
    have hEn : |alg2Output (alg2K ε') (μneg ω) - ∫ x, alg3NegQuarter σ (m ω) X x ∂P₀|
        ≤ 4 * ε' := by
      have hb := alg2_error_bound P₀ C D ε' (alg3NegQuarter σ (m ω) X) (μneg ω)
        hC hD1 hD2 hε'0 hε'1 hqmem.1 hnnNeg hNω
      calc |alg2Output (alg2K ε') (μneg ω) - ∫ x, alg3NegQuarter σ (m ω) X x ∂P₀|
          ≤ ε' * (l2norm P₀ (alg3NegQuarter σ (m ω) X) + 1) ^ 2 := hb
        _ ≤ ε' * 4 := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hε'0)
            have h1 : l2norm P₀ (alg3NegQuarter σ (m ω) X) + 1 ≤ 2 := by linarith [hql2.1]
            have h2 : 0 ≤ l2norm P₀ (alg3NegQuarter σ (m ω) X) + 1 :=
              add_nonneg (Real.sqrt_nonneg _) (by norm_num)
            calc (l2norm P₀ (alg3NegQuarter σ (m ω) X) + 1) ^ 2 ≤ 2 ^ 2 :=
                  pow_le_pow_left₀ h2 h1 2
              _ = 4 := by norm_num
        _ = 4 * ε' := by ring
    have hEp : |alg2Output (alg2K ε') (μpos ω) - ∫ x, alg3PosQuarter σ (m ω) X x ∂P₀|
        ≤ 4 * ε' := by
      have hb := alg2_error_bound P₀ C D ε' (alg3PosQuarter σ (m ω) X) (μpos ω)
        hC hD1 hD2 hε'0 hε'1 hqmem.2 hnnPos hPω
      calc |alg2Output (alg2K ε') (μpos ω) - ∫ x, alg3PosQuarter σ (m ω) X x ∂P₀|
          ≤ ε' * (l2norm P₀ (alg3PosQuarter σ (m ω) X) + 1) ^ 2 := hb
        _ ≤ ε' * 4 := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hε'0)
            have h1 : l2norm P₀ (alg3PosQuarter σ (m ω) X) + 1 ≤ 2 := by linarith [hql2.2]
            have h2 : 0 ≤ l2norm P₀ (alg3PosQuarter σ (m ω) X) + 1 :=
              add_nonneg (Real.sqrt_nonneg _) (by norm_num)
            calc (l2norm P₀ (alg3PosQuarter σ (m ω) X) + 1) ^ 2 ≤ 2 ^ 2 :=
                  pow_le_pow_left₀ h2 h1 2
              _ = 4 := by norm_num
        _ = 4 * ε' := by ring
    set Aneg : ℝ := alg2Output (alg2K ε') (μneg ω) with hAneg
    set Apos : ℝ := alg2Output (alg2K ε') (μpos ω) with hApos
    set Ineg : ℝ := ∫ x, alg3NegQuarter σ (m ω) X x ∂P₀ with hIneg
    set Ipos : ℝ := ∫ x, alg3PosQuarter σ (m ω) X x ∂P₀ with hIpos
    set IX : ℝ := ∫ x, X x ∂P₀ with hIX
    have hEn' : |Aneg - Ineg| ≤ 4 * ε' := by simpa only [hAneg, hIneg] using hEn
    have hEp' : |Apos - Ipos| ≤ 4 * ε' := by simpa only [hApos, hIpos] using hEp
    have hXint : Integrable X P₀ := hXmem.integrable (by norm_num)
    have hrec := theorem_5_recombination P₀ X hXint σ (m ω) hσ0
    have hIneg4 : (∫ x, -(truncLt 0 (alg3B σ (m ω) X) x) ∂P₀) = 4 * Ineg := by
      have hfun : (fun x => -(truncLt 0 (alg3B σ (m ω) X) x))
          = (fun x => 4 * alg3NegQuarter σ (m ω) X x) := by
        funext x; unfold alg3NegQuarter; ring
      rw [hfun, integral_const_mul, hIneg]
    have hIpos4 : (∫ x, truncGe 0 (alg3B σ (m ω) X) x ∂P₀) = 4 * Ipos := by
      have hfun : (fun x => truncGe 0 (alg3B σ (m ω) X) x)
          = (fun x => 4 * alg3PosQuarter σ (m ω) X x) := by
        funext x; unfold alg3PosQuarter; ring
      rw [hfun, integral_const_mul, hIpos]
    have hIX4 : IX = σ * (m ω - 4 * Ineg + 4 * Ipos) := by
      rw [hIX, hrec, hIneg4, hIpos4]
    have hAunfold : alg3Output σ (m ω) (alg2K ε') (μneg ω) (μpos ω)
        = σ * (m ω - 4 * Aneg + 4 * Apos) := by
      unfold alg3Output
      rw [← hAneg, ← hApos]
    have hdiff : alg3Output σ (m ω) (alg2K ε') (μneg ω) (μpos ω) - IX
        = σ * ((-4) * (Aneg - Ineg) + 4 * (Apos - Ipos)) := by
      rw [hAunfold, hIX4]; ring
    have htri : |alg3Output σ (m ω) (alg2K ε') (μneg ω) (μpos ω) - IX|
        ≤ σ * (4 * |Aneg - Ineg| + 4 * |Apos - Ipos|) := by
      rw [hdiff, abs_mul, abs_of_pos hσ0]
      have h1 := abs_add_le ((-4) * (Aneg - Ineg)) (4 * (Apos - Ipos))
      simp only [abs_mul, abs_neg, abs_four] at h1
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hσ0)
    have hfinal : |alg3Output σ (m ω) (alg2K ε') (μneg ω) (μpos ω) - IX| ≤ ε := by
      calc |alg3Output σ (m ω) (alg2K ε') (μneg ω) (μpos ω) - IX|
          ≤ σ * (4 * |Aneg - Ineg| + 4 * |Apos - Ipos|) := htri
        _ ≤ σ * (4 * (4 * ε') + 4 * (4 * ε')) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hσ0)
              linarith [hEn', hEp']
        _ = ε := by
              rw [hε']; field_simp; ring
    simpa only [hIX] using hfinal
  have hNle : P N ≤ (1 / 9 : ENNReal) := by rw [hN]; exact hfailNeg
  have hPle : P Pset ≤ (1 / 9 : ENNReal) := by rw [hPset]; exact hfailPos
  have hEcle : P Eᶜ ≤ (1 / 9 : ENNReal) := by
    have hmeas : Measurable (fun y : ℝ => |y - c|) :=
      (measurable_id.sub measurable_const).abs
    have hset : MeasurableSet {y : ℝ | 3 < |y - c|} := measurableSet_lt measurable_const hmeas
    have hset' : MeasurableSet {y : ℝ | 3 ≤ |y - c|} := measurableSet_le measurable_const hmeas
    have hEq : Eᶜ = m ⁻¹' {y : ℝ | 3 < |y - c|} := by
      ext ω
      simp only [hE, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage, not_le]
    rw [hEq, ← Measure.map_apply hm hset, hmap, Measure.map_apply (hXm.div_const σ) hset]
    refine (measure_mono ?_).trans (theorem_5_chebyshev P₀ X hXm hXmem σ hvar hσ0)
    intro x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    linarith
  set U : Set Ω := Eᶜ ∪ N ∪ Pset with hU
  have hUle : P U ≤ (1 / 3 : ENNReal) := by
    have h1 : P U ≤ P (Eᶜ ∪ N) + P Pset := measure_union_le (Eᶜ ∪ N) Pset
    have h2 : P (Eᶜ ∪ N) ≤ P Eᶜ + P N := measure_union_le Eᶜ N
    calc P U ≤ P (Eᶜ ∪ N) + P Pset := h1
      _ ≤ (P Eᶜ + P N) + P Pset := add_le_add h2 (le_refl _)
      _ ≤ ((1 / 9 : ENNReal) + (1 / 9 : ENNReal)) + (1 / 9 : ENNReal) :=
            add_le_add (add_le_add hEcle hNle) hPle
      _ = 1 / 3 := by
            rw [show (1 / 9 : ENNReal) = ((1 / 9 : NNReal) : ENNReal) from by
                  rw [ENNReal.coe_div (by norm_num)]; norm_num,
                show (1 / 3 : ENNReal) = ((1 / 3 : NNReal) : ENNReal) from by
                  rw [ENNReal.coe_div (by norm_num)]; norm_num,
                ← ENNReal.coe_add, ← ENNReal.coe_add]
            exact_mod_cast (by norm_num : (1 / 9 : NNReal) + 1 / 9 + 1 / 9 = 1 / 3)
  have hcompl : Uᶜ = E ∩ Nᶜ ∩ Psetᶜ := by
    ext ω; simp only [hU, Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff]; tauto
  have hsub : Uᶜ ⊆ Final := by rw [hcompl]; exact hgood
  have hFinalge : P Uᶜ ≤ P Final := measure_mono hsub
  have hcomple : (1 : ENNReal) - P U ≤ P Uᶜ := by
    have h1 : (1 : ENNReal) ≤ P U + P Uᶜ := by
      have h := measure_union_le (μ := P) U Uᶜ
      rwa [Set.union_compl_self, measure_univ] at h
    exact (tsub_le_iff_right).mpr (by rw [add_comm]; exact h1)
  have hmain : (2 / 3 : ENNReal) ≤ P Final := by
    calc (2 / 3 : ENNReal) ≤ 1 - (1 / 3 : ENNReal) := by
          have hc : (1 / 3 : ENNReal) ≠ ⊤ := by
            rw [show (1 / 3 : ENNReal) = ((1 / 3 : NNReal) : ENNReal) from by
                  rw [ENNReal.coe_div (by norm_num)]; norm_num]
            exact ENNReal.coe_ne_top
          have hcb : (1 / 3 : ENNReal) ≤ 1 := by
            rw [show (1 / 3 : ENNReal) = ((1 / 3 : NNReal) : ENNReal) from by
                  rw [ENNReal.coe_div (by norm_num)]; norm_num,
                ← ENNReal.coe_one]
            exact ENNReal.coe_le_coe.mpr
              (by exact_mod_cast (by norm_num : (1 : ℝ) / 3 ≤ 1))
          rw [ENNReal.le_sub_iff_add_le_right hc hcb]
          rw [show (2 / 3 : ENNReal) + (1 / 3 : ENNReal) = 1 from by
                rw [show (2 / 3 : ENNReal) = ((2 / 3 : NNReal) : ENNReal) from by
                      rw [ENNReal.coe_div (by norm_num)]; norm_num,
                    show (1 / 3 : ENNReal) = ((1 / 3 : NNReal) : ENNReal) from by
                      rw [ENNReal.coe_div (by norm_num)]; norm_num,
                    ← ENNReal.coe_add, ← ENNReal.coe_one]
                exact_mod_cast (by norm_num : (2 / 3 : NNReal) + 1 / 3 = 1)]
      _ ≤ 1 - P U := tsub_le_tsub_left hUle 1
      _ ≤ P Uᶜ := hcomple
      _ ≤ P Final := hFinalge
  simpa only [hFinal, hε'] using hmain
