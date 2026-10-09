-- Prove2me | solution 1 for TroppMatrixConcentration.ch7_intrinsic_bernstein_expectation
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:41:45.820979+00:00
-- url     : https://prove2.me/submissions/7620d2d0-0738-4fb1-936e-1589e5e9731b

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic
import Theorems.Thm_TroppMatrixConcentration_ch7_intrinsic_bernstein
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TroppMatrixConcentration.Ch7IBE

open Matrix

/-- A matrix dominating `∫ Z Zᴴ` (or any integral of PSD matrices) in the Loewner order is PSD. -/
lemma ibe_psd_of_loewnerLE {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Ω → Matrix d d ℂ) (hF : ∀ ω, (F ω).PosSemidef) (V : Matrix d d ℂ)
    (h : loewnerLE (∫ ω, F ω ∂μ) V) : V.PosSemidef := by
  have h0 : (0 : Matrix d d ℂ) ≤ ∫ ω, F ω ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => (hF ω).nonneg)
  have hI : (∫ ω, F ω ∂μ).PosSemidef := Matrix.nonneg_iff_posSemidef.mp h0
  have : V = (V - ∫ ω, F ω ∂μ) + ∫ ω, F ω ∂μ := by abel
  rw [this]
  exact PosSemidef.add h hI

/-- For a PSD matrix, the spectral norm is at most the trace. -/
lemma ibe_norm_le_trace {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {P : Matrix d d ℂ} (hP : P.PosSemidef) : ‖P‖ ≤ (trace P).re := by
  have hH : P.IsHermitian := hP.isHermitian
  have hsa : IsSelfAdjoint P := hH
  have htr : (trace P).re = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues]; simp
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hP.eigenvalues_nonneg i
  have key : ∃ i, ‖P‖ ≤ hH.eigenvalues i := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hsa with h | h
    · rw [hH.spectrum_real_eq_range_eigenvalues] at h
      obtain ⟨i, hi⟩ := h
      exact ⟨i, hi.ge⟩
    · rw [hH.spectrum_real_eq_range_eigenvalues] at h
      obtain ⟨i, hi⟩ := h
      refine ⟨i, ?_⟩
      have := hnn i
      have := norm_nonneg P
      linarith
  obtain ⟨i, hi⟩ := key
  rw [htr]
  exact hi.trans (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i))

/-- A block-diagonal matrix with PSD blocks is PSD. -/
lemma ibe_posSemidef_fromBlocks_diag {m n : Type*} [Fintype m] [Fintype n]
    {P : Matrix m m ℂ} {Q : Matrix n n ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : (fromBlocks P 0 0 Q).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (IsHermitian.fromBlocks hP.1 (by simp) hQ.1) fun x => ?_
  have e : star x ⬝ᵥ (fromBlocks P 0 0 Q *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (P *ᵥ (x ∘ Sum.inl)) +
        star (x ∘ Sum.inr) ⬝ᵥ (Q *ᵥ (x ∘ Sum.inr)) := by
    rw [fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type]
  rw [e]
  exact add_nonneg (hP.dotProduct_mulVec_nonneg _) (hQ.dotProduct_mulVec_nonneg _)

/-- The intrinsic dimension of a nonzero PSD matrix is at least one. -/
lemma ibe_one_le_intrinsicDimension {d : Type*} [Fintype d] [DecidableEq d]
    {P : Matrix d d ℂ} (hP : P.PosSemidef) (hne : P ≠ 0) : 1 ≤ intrinsicDimension P := by
  have hpos : 0 < ‖P‖ := norm_pos_iff.mpr hne
  have : Nonempty d := by
    by_contra hd
    rw [not_nonempty_iff] at hd
    exact hne (Subsingleton.elim _ _)
  unfold intrinsicDimension spectralNorm
  rw [le_div_iff₀ hpos, one_mul]
  exact ibe_norm_le_trace hP

/-- Exponent comparison: for `τ ≥ μ₀ > 0`, the Bernstein exponent dominates a linear one. -/
lemma ibe_exponent_le {v L μ₀ τ : ℝ} (hv : 0 < v) (hL : 0 ≤ L) (hμ : 0 < μ₀) (hτ : μ₀ ≤ τ) :
    -(τ ^ 2 / 2) / (v + L * τ / 3) ≤ -((μ₀ / 2) / (v + L * μ₀ / 3)) * τ := by
  have hA : 0 < v + L * μ₀ / 3 := by positivity
  have hB : 0 < v + L * τ / 3 := by have : 0 < τ := hμ.trans_le hτ; positivity
  rw [neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_div_iff₀ hA hB]
  have : 0 < τ := hμ.trans_le hτ
  nlinarith [mul_le_mul_of_nonneg_left hτ (le_of_lt (mul_pos this hv))]

/-- The tail integral of an exponential. -/
lemma ibe_integral_exp {K c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), K * Real.exp (-c * t) = K / c := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -c < 0) 0]
  simp
  field_simp

lemma ibe_integrable_exp {K c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => K * Real.exp (-c * t)) (Set.Ioi 0) :=
  (exp_neg_integrableOn_Ioi 0 hc).const_mul K

/-- The final scalar bookkeeping. -/
lemma ibe_scalar {v L ℓ r : ℝ} (hv : 0 < v) (hL : 0 ≤ L) (hℓ : 1 / 2 ≤ ℓ) (hr : 0 ≤ r)
    (hexp : Real.exp (-ℓ) = 1 / (1 + r)) :
    let μ₀ := 2 * Real.sqrt (ℓ * v) + 2 * ℓ * L
    let c := (μ₀ / 2) / (v + L * μ₀ / 3)
    Real.sqrt v + L / 3 ≤ μ₀ ∧ 0 < μ₀ ∧ 0 < c ∧
    μ₀ + 4 * r * Real.exp (-c * μ₀) / c ≤
      20 * (Real.sqrt (v * ℓ) + L * ℓ) := by
  intro μ₀ c
  set s := Real.sqrt (ℓ * v) with hs
  have hℓ0 : 0 < ℓ := by linarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hss : s ^ 2 = ℓ * v := Real.sq_sqrt (by positivity)
  have hsv : Real.sqrt (v * ℓ) = s := by rw [mul_comm]
  have hμ : 0 < μ₀ := by positivity
  have hA : 0 < v + L * μ₀ / 3 := by positivity
  have hc : 0 < c := by positivity
  refine ⟨?_, hμ, hc, ?_⟩
  · -- `√v ≤ 2 √(ℓ v)` since `ℓ ≥ 1/4`
    have h1 : Real.sqrt v ≤ 2 * s := by
      rw [hs, show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : L / 3 ≤ 2 * ℓ * L := by nlinarith
    show Real.sqrt v + L / 3 ≤ 2 * s + 2 * ℓ * L
    linarith
  · -- `c μ₀ ≥ ℓ`
    have hcμ : ℓ ≤ c * μ₀ := by
      show ℓ ≤ (μ₀ / 2) / (v + L * μ₀ / 3) * μ₀
      rw [div_mul_eq_mul_div, le_div_iff₀ hA]
      have : μ₀ * μ₀ ≥ 2 * s * (2 * s) + 2 * ℓ * L * μ₀ := by
        show (2 * s + 2 * ℓ * L) * μ₀ ≥ _
        have : 2 * s ≤ μ₀ := by show 2 * s ≤ 2 * s + 2 * ℓ * L; nlinarith
        nlinarith
      nlinarith
    have he : Real.exp (-c * μ₀) ≤ 1 / (1 + r) := by
      rw [← hexp]; exact Real.exp_le_exp.mpr (by linarith)
    have h4 : 4 * r * Real.exp (-c * μ₀) ≤ 4 := by
      calc 4 * r * Real.exp (-c * μ₀) ≤ 4 * r * (1 / (1 + r)) := by gcongr
        _ ≤ 4 := by
          rw [mul_one_div, div_le_iff₀ (by linarith)]; linarith
    have hinvc : 1 / c = 2 * v / μ₀ + 2 * L / 3 := by
      show 1 / ((μ₀ / 2) / (v + L * μ₀ / 3)) = _
      field_simp
    have h2v : 2 * v / μ₀ ≤ 2 * s := by
      rw [div_le_iff₀ hμ]
      show 2 * v ≤ 2 * s * (2 * s + 2 * ℓ * L)
      nlinarith [mul_nonneg (mul_nonneg hs0.le hℓ0.le) hL]
    have hterm : 4 * r * Real.exp (-c * μ₀) / c ≤ 4 * (2 * s + 2 * L / 3) := by
      rw [div_eq_mul_one_div, hinvc]
      have hnn : 0 ≤ 2 * v / μ₀ + 2 * L / 3 := by positivity
      calc 4 * r * Real.exp (-c * μ₀) * (2 * v / μ₀ + 2 * L / 3)
          ≤ 4 * (2 * v / μ₀ + 2 * L / 3) := by gcongr
        _ ≤ 4 * (2 * s + 2 * L / 3) := by gcongr
    rw [hsv]
    show 2 * s + 2 * ℓ * L + 4 * r * Real.exp (-c * μ₀) / c ≤ 20 * (s + L * ℓ)
    nlinarith

end TroppMatrixConcentration.Ch7IBE

open TroppMatrixConcentration TroppMatrixConcentration.Ch7IBE

theorem solution :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {m n N : ℕ} [NeZero m] [NeZero n]
      (S : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ) (L : ℝ), 0 ≤ L →
    ∀ (V₁ : Matrix (Fin m) (Fin m) ℂ) (V₂ : Matrix (Fin n) (Fin n) ℂ),
      (V₁ ≠ 0 ∨ V₂ ≠ 0) →
      (∀ k, Measurable (S k)) → iIndepFun S μ →
      (∀ k, (∫ ω, S k ω ∂μ) = 0) →
      (∀ k, ∀ᵐ ω ∂μ, spectralNorm (S k ω) ≤ L) →
      loewnerLE (∫ ω, (∑ k, S k ω) * (∑ k, S k ω).conjTranspose ∂μ) V₁ →
      loewnerLE (∫ ω, (∑ k, S k ω).conjTranspose * (∑ k, S k ω) ∂μ) V₂ →
      let r := intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂)
      let v := max (spectralNorm V₁) (spectralNorm V₂)
      (∫ ω, spectralNorm (∑ k, S k ω) ∂μ) ≤
        C * (Real.sqrt (v * Real.log (1 + r)) + L * Real.log (1 + r)) := by
  refine ⟨20, by norm_num, ?_⟩
  intro Ω _ μ _ m n N _ _ S L hL V₁ V₂ hV hMeas hIndep hMean hBound hVar₁ hVar₂ r v
  -- PSD-ness of the variance proxies
  have hV₁ : V₁.PosSemidef := ibe_psd_of_loewnerLE _
    (fun ω => Matrix.posSemidef_self_mul_conjTranspose _) V₁ hVar₁
  have hV₂ : V₂.PosSemidef := ibe_psd_of_loewnerLE _
    (fun ω => Matrix.posSemidef_conjTranspose_mul_self _) V₂ hVar₂
  -- `v > 0`
  have hv : 0 < v := by
    rcases hV with h | h
    · exact lt_max_of_lt_left (norm_pos_iff.mpr h)
    · exact lt_max_of_lt_right (norm_pos_iff.mpr h)
  -- `r ≥ 1`
  have hr : 1 ≤ r := by
    apply ibe_one_le_intrinsicDimension (ibe_posSemidef_fromBlocks_diag hV₁ hV₂)
    intro h0
    rw [← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at h0
    rcases hV with h | h
    · exact h h0.1
    · exact h h0.2.2.2
  set ℓ := Real.log (1 + r) with hℓdef
  have hℓ : 1 / 2 ≤ ℓ := by
    have h2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  have hexp : Real.exp (-ℓ) = 1 / (1 + r) := by
    rw [Real.exp_neg, hℓdef, Real.exp_log (by linarith), one_div]
  obtain ⟨hμ₀, hμpos, hc, hfinal⟩ := ibe_scalar hv hL hℓ (by linarith) hexp
  set μ₀ := 2 * Real.sqrt (ℓ * v) + 2 * ℓ * L with hμ₀def
  set c := (μ₀ / 2) / (v + L * μ₀ / 3) with hcdef
  -- the imported tail bound
  have htail := (ch7_intrinsic_bernstein μ S L hL V₁ V₂ hV hMeas hIndep hMean hBound
    hVar₁ hVar₂).2.2
  -- reduce to integrable case
  by_cases hint : Integrable (fun ω => spectralNorm (∑ k, S k ω)) μ
  swap
  · rw [integral_undef hint]
    have : 0 ≤ Real.sqrt (v * ℓ) + L * ℓ := by
      have : 0 ≤ ℓ := by linarith
      positivity
    linarith
  set W : Ω → ℝ := fun ω => max (spectralNorm (∑ k, S k ω) - μ₀) 0 with hWdef
  have hWint : Integrable W μ := (hint.sub (integrable_const μ₀)).pos_part
  have hsplit : (∫ ω, spectralNorm (∑ k, S k ω) ∂μ) ≤ μ₀ + ∫ ω, W ω ∂μ := by
    have h1 : (∫ ω, spectralNorm (∑ k, S k ω) ∂μ) ≤ ∫ ω, (μ₀ + W ω) ∂μ :=
      integral_mono hint ((integrable_const μ₀).add hWint) fun ω => by
        simp only [hWdef]
        have := le_max_left (spectralNorm (∑ k, S k ω) - μ₀) 0
        linarith
    rw [integral_add (integrable_const μ₀) hWint, integral_const] at h1
    simpa using h1
  have hW : (∫ ω, W ω ∂μ) ≤ 4 * r * Real.exp (-c * μ₀) / c := by
    rw [hWint.integral_eq_integral_meas_le (Filter.Eventually.of_forall fun ω => le_max_right _ _)]
    have hK : ∫ t in Set.Ioi (0 : ℝ), (4 * r * Real.exp (-c * μ₀)) * Real.exp (-c * t) =
        4 * r * Real.exp (-c * μ₀) / c := ibe_integral_exp hc
    rw [← hK]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => measureReal_nonneg)
      (ibe_integrable_exp hc) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht : 0 < t := ht
    have hsub : {a | t ≤ W a} ⊆ {ω | t + μ₀ ≤ spectralNorm (∑ k, S k ω)} := by
      intro a ha
      simp only [Set.mem_ofPred_eq, hWdef] at ha ⊢
      rcases le_max_iff.mp ha with h | h
      · linarith
      · linarith
    calc μ.real {a | t ≤ W a} ≤ μ.real {ω | t + μ₀ ≤ spectralNorm (∑ k, S k ω)} :=
          measureReal_mono hsub
      _ ≤ 4 * r * Real.exp (-((t + μ₀) ^ 2 / 2) / (v + L * (t + μ₀) / 3)) :=
          htail (t + μ₀) (by linarith)
      _ ≤ 4 * r * Real.exp (-c * (t + μ₀)) := by
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (ibe_exponent_le hv hL hμpos (by linarith))) (by linarith)
      _ = 4 * r * Real.exp (-c * μ₀) * Real.exp (-c * t) := by
          rw [show -c * (t + μ₀) = -c * μ₀ + -c * t by ring, Real.exp_add]; ring
  calc (∫ ω, spectralNorm (∑ k, S k ω) ∂μ) ≤ μ₀ + 4 * r * Real.exp (-c * μ₀) / c := by
        linarith
    _ ≤ 20 * (Real.sqrt (v * ℓ) + L * ℓ) := hfinal
