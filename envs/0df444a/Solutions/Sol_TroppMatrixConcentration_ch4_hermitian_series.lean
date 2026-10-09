-- Prove2me | solution 1 for TroppMatrixConcentration.ch4_hermitian_series
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:13:20.028466+00:00
-- url     : https://prove2.me/submissions/59c1319b-775c-4d79-956a-f5f1bcc3b8f9

import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws
import Definitions.Def_TroppMatrixConcentration_dilation
import Theorems.Thm_TroppMatrixConcentration_master_bounds
import Theorems.Thm_TroppMatrixConcentration_ch4_gaussian_mgf_cgf
import Theorems.Thm_TroppMatrixConcentration_ch4_rademacher_mgf_cgf
import Theorems.Thm_TroppMatrixConcentration_ch8_trace_exp_monotone
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option autoImplicit false

namespace TroppMatrixConcentration

/-- Real spectral values of a matrix are bounded in absolute value by the operator norm. -/
lemma ch4hs_abs_le_norm {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ) {x : ℝ}
    (hx : x ∈ spectrum ℝ B) : |x| ≤ ‖B‖ := by
  have h : algebraMap ℝ ℂ x ∈ spectrum ℂ B := (spectrum.algebraMap_mem_iff ℂ).mpr hx
  have := spectrum.norm_le_norm_of_mem h
  simpa using this

lemma ch4hs_traceExp_eq_sum {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [traceExp, matrixExp, ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re]

lemma ch4hs_traceExp_le {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian)
    {c : ℝ} (hc : 0 ≤ c) : traceExp (c • B) ≤ d * Real.exp (c * ‖B‖) := by
  rw [ch4hs_traceExp_eq_sum B hB c]
  calc ∑ i, Real.exp (c * hB.eigenvalues i) ≤ ∑ _i : Fin d, Real.exp (c * ‖B‖) := by
        apply Finset.sum_le_sum
        intro i _
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hc
        exact (le_abs_self _).trans (ch4hs_abs_le_norm B (hB.eigenvalues_mem_spectrum_real i))
    _ = d * Real.exp (c * ‖B‖) := by simp

lemma ch4hs_traceExp_pos {d : ℕ} [NeZero d] (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    0 < traceExp H := by
  have h := ch4hs_traceExp_eq_sum H hH 1
  rw [one_smul] at h
  rw [h]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

lemma ch4hs_norm_exp_le {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (s : ℝ) : ‖matrixExp (s • A)‖ ≤ Real.exp (s * ‖A‖) + Real.exp (-(s * ‖A‖)) := by
  have hsA : (s • A).IsHermitian := hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))
  have h1 : ‖matrixExp (s • A)‖ ≤ Real.exp (|s| * ‖A‖) := by
    rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hsA]
    apply norm_cfc_le (Real.exp_pos _).le
    intro x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    apply Real.exp_le_exp.mpr
    calc x ≤ |x| := le_abs_self x
      _ ≤ ‖s • A‖ := ch4hs_abs_le_norm _ hx
      _ = |s| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs] at h1
    linarith [Real.exp_pos (-(s * ‖A‖))]
  · rw [abs_of_nonpos hs, neg_mul] at h1
    linarith [Real.exp_pos (s * ‖A‖)]

lemma ch4hs_exp_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (g : Ω → ℝ) (hg : Measurable g)
    (hexp : ∀ c : ℝ, Integrable (fun ω => Real.exp (c * g ω)) μ) (θ : ℝ) :
    Integrable (fun ω => matrixExp (θ • (g ω • A))) μ := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have e : (fun ω => matrixExp (θ • (g ω • A))) = fun ω => matrixExp ((θ * g ω) • A) := by
    funext ω
    rw [smul_smul]
  rw [e]
  have hb : Integrable (fun ω => Real.exp ((θ * ‖A‖) * g ω) +
      Real.exp ((-(θ * ‖A‖)) * g ω)) μ := (hexp _).add (hexp _)
  refine hb.mono' ?_ ?_
  · have hcont : Continuous (fun s : ℝ => matrixExp (s • A)) := by
      dsimp [matrixExp]
      fun_prop
    exact hcont.comp_aestronglyMeasurable (measurable_const.mul hg).aestronglyMeasurable
  · refine ae_of_all _ (fun ω => ?_)
    have h := ch4hs_norm_exp_le A hA (θ * g ω)
    have e1 : θ * ‖A‖ * g ω = θ * g ω * ‖A‖ := by ring
    have e2 : -(θ * ‖A‖) * g ω = -(θ * g ω * ‖A‖) := by ring
    simp only [e1, e2]
    exact h

lemma ch4hs_second_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {d N : ℕ} (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (g : Fin N → Ω → ℝ) (hMeas : ∀ k, Measurable (g k)) (hIndep : iIndepFun g μ)
    (h2 : ∀ k, MemLp (g k) 2 μ) (h0 : ∀ k, ∫ ω, g k ω ∂μ = 0)
    (h1 : ∀ k, ∫ ω, g k ω ^ 2 ∂μ = 1) :
    ∫ ω, (∑ k, g k ω • A k) ^ 2 ∂μ = ∑ k, A k ^ 2 := by
  have hexp : ∀ ω, (∑ k, g k ω • A k) ^ 2 = ∑ j, ∑ k, (g j ω * g k ω) • (A j * A k) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm]
  have hint : ∀ j k, Integrable (fun ω => g j ω * g k ω) μ := fun j k =>
    (h2 j).integrable_mul (h2 k)
  have hcorr : ∀ j k, ∫ ω, g j ω * g k ω ∂μ = if j = k then 1 else 0 := by
    intro j k
    split_ifs with hjk
    · subst hjk
      simpa [sq] using h1 j
    · rw [(hIndep.indepFun hjk).integral_fun_mul_eq_mul_integral
        (hMeas j).aestronglyMeasurable (hMeas k).aestronglyMeasurable, h0 j, zero_mul]
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => (hint j k).smul_const _))]
  have hinner : ∀ j, ∫ ω, ∑ k, (g j ω * g k ω) • (A j * A k) ∂μ = A j ^ 2 := by
    intro j
    rw [integral_finsetSum _ (fun k _ => (hint j k).smul_const _)]
    simp_rw [integral_smul_const, hcorr]
    simp [sq]
  simp_rw [hinner]

lemma ch4hs_gauss_facts {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : Measurable g) (hL : standardGaussianLaw μ g) :
    MemLp g 2 μ ∧ ∫ ω, g ω ∂μ = 0 ∧ ∫ ω, g ω ^ 2 ∂μ = 1 ∧
      ∀ c : ℝ, Integrable (fun ω => Real.exp (c * g ω)) μ := by
  unfold standardGaussianLaw at hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)
    rw [← hL] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id hg.aemeasurable).1 h
  · have h := integral_id_gaussianReal (μ := 0) (v := 1)
    rw [← hL, integral_map hg.aemeasurable (by fun_prop)] at h
    exact h
  · have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simp only [id, integral_id_gaussianReal, sub_zero] at h
    rw [← hL, integral_map hg.aemeasurable (by fun_prop)] at h
    simpa using h
  · intro c
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) c
    rw [← hL] at h
    exact (integrable_map_measure (by fun_prop) hg.aemeasurable).1 h

lemma ch4hs_rad_facts {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : Measurable g) (hL : rademacherLaw μ g) :
    MemLp g 2 μ ∧ ∫ ω, g ω ∂μ = 0 ∧ ∫ ω, g ω ^ 2 ∂μ = 1 ∧
      ∀ c : ℝ, Integrable (fun ω => Real.exp (c * g ω)) μ := by
  unfold rademacherLaw at hL
  have hS : MeasurableSet {x : ℝ | x = 1 ∨ x = -1} :=
    (measurableSet_singleton 1).union (measurableSet_singleton (-1))
  have hpm : ∀ᵐ ω ∂μ, g ω = 1 ∨ g ω = -1 := by
    rw [← ae_map_iff hg.aemeasurable hS, hL, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inl rfl)) _
    · exact Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inr rfl)) _
  have hbd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1 := hpm.mono fun ω h => by
    rcases h with h | h <;> simp [h]
  have hsq : ∀ᵐ ω ∂μ, g ω ^ 2 = 1 := hpm.mono fun ω h => by
    rcases h with h | h <;> simp [h]
  refine ⟨MemLp.of_bound hg.aestronglyMeasurable 1 hbd, ?_, ?_, ?_⟩
  · have h : ∫ x, x ∂(Measure.map g μ) = ∫ ω, g ω ∂μ :=
      integral_map hg.aemeasurable aestronglyMeasurable_id
    have hi1 : Integrable (fun x : ℝ => x) ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    have hi2 : Integrable (fun x : ℝ => x) ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    rw [← h, hL, integral_add_measure hi1 hi2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
    simp
  · rw [integral_congr_ae hsq]
    simp
  · intro c
    have hb : ∀ᵐ ω ∂μ, ‖Real.exp (c * g ω)‖ ≤ Real.exp |c| := hpm.mono fun ω h => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      rcases h with h | h
      · rw [h, mul_one]; exact le_abs_self c
      · rw [h, mul_neg_one]; exact neg_le_abs c
    exact memLp_one_iff_integrable.1 (MemLp.of_bound
      (Real.continuous_exp.comp_aestronglyMeasurable
        (measurable_const.mul hg).aestronglyMeasurable) _ hb)

lemma ch4hs_scalar {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ θ : ℝ, 0 < θ → x ≤ a / θ + θ * b / 2) : x ≤ Real.sqrt (2 * b * a) := by
  by_contra hcon
  push Not at hcon
  have hs0 := Real.sqrt_nonneg (2 * b * a)
  have hx : 0 < x := lt_of_le_of_lt hs0 hcon
  rcases ha.eq_or_lt with rfl | ha'
  · rcases hb.eq_or_lt with rfl | hb'
    · have := h 1 one_pos
      simp at this
      linarith
    · have := h (x / b) (div_pos hx hb')
      rw [zero_div, zero_add, div_mul_cancel₀ _ hb'.ne'] at this
      linarith
  · rcases hb.eq_or_lt with rfl | hb'
    · have := h (2 * a / x) (by positivity)
      have e : a / (2 * a / x) = x / 2 := by field_simp
      rw [e] at this
      simp at this
      linarith
    · have hs : 0 < Real.sqrt (2 * b * a) := Real.sqrt_pos.mpr (by positivity)
      have hss : Real.sqrt (2 * b * a) ^ 2 = 2 * b * a := Real.sq_sqrt (by positivity)
      have := h (Real.sqrt (2 * b * a) / b) (div_pos hs hb')
      generalize Real.sqrt (2 * b * a) = s at hs hss this hcon
      have e : a / (s / b) + s / b * b / 2 = s := by
        field_simp
        nlinarith [hss]
      linarith

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ k, (A k).IsHermitian)
    (g : Fin N → Ω → ℝ) (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ)
    (hLaw : (∀ k, standardGaussianLaw μ (g k)) ∨ (∀ k, rademacherLaw μ (g k))) :
    let Y := fun ω => ∑ k, g k ω • A k
    let v := hermitianSecondMoment μ Y
    v = spectralNorm (∑ k, A k ^ 2) ∧
    (∫ ω, lambdaMax (Y ω) ∂μ) ≤ Real.sqrt (2 * v * Real.log d) ∧
    ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
      gaussianSeriesTail d v t := by
  intro Y v
  have hfacts : ∀ k, MemLp (g k) 2 μ ∧ ∫ ω, g k ω ∂μ = 0 ∧ ∫ ω, g k ω ^ 2 ∂μ = 1 ∧
      ∀ c : ℝ, Integrable (fun ω => Real.exp (c * g k ω)) μ := by
    intro k
    rcases hLaw with h | h
    · exact ch4hs_gauss_facts μ (g k) (hMeas k) (h k)
    · exact ch4hs_rad_facts μ (g k) (hMeas k) (h k)
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le one_pos hd
  have hBherm : (∑ k, A k ^ 2).IsHermitian := isSelfAdjoint_sum _ (fun k _ => (hA k).pow 2)
  have hv : v = ‖∑ k, A k ^ 2‖ := by
    show spectralNorm (∫ ω, (∑ k, g k ω • A k) ^ 2 ∂μ) = ‖∑ k, A k ^ 2‖
    rw [ch4hs_second_moment μ A g hMeas hIndep (fun k => (hfacts k).1)
      (fun k => (hfacts k).2.1) (fun k => (hfacts k).2.2.1)]
    rfl
  have hv0 : 0 ≤ v := hv ▸ norm_nonneg _
  let X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ := fun k ω => g k ω • A k
  have hsmulMeas : ∀ k, Measurable (fun s : ℝ => s • A k) := fun k =>
    (continuous_id.smul continuous_const).measurable
  have hXMeas : ∀ k, Measurable (X k) := fun k => (hsmulMeas k).comp (hMeas k)
  have hXHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian := fun k =>
    ae_of_all _ (fun ω => (hA k).smul (isSelfAdjoint_iff.mpr (star_trivial _)))
  have hXInt : ∀ k, Integrable (X k) μ := fun k =>
    (MemLp.integrable one_le_two (hfacts k).1).smul_const (A k)
  have hXIndep : iIndepFun X μ := hIndep.comp (fun k s => s • A k) hsmulMeas
  have hXExp : ∀ θ : ℝ, ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ := fun θ k =>
    ch4hs_exp_integrable μ (A k) (hA k) (g k) (hMeas k) (hfacts k).2.2.2 θ
  have hcumH : ∀ θ : ℝ, (cumulantSum μ X θ).IsHermitian := fun θ =>
    isSelfAdjoint_sum _ (fun k _ => by unfold matrixLog; exact IsSelfAdjoint.cfc)
  have hcgf : ∀ θ : ℝ, traceExp (cumulantSum μ X θ) ≤ d * Real.exp (θ ^ 2 / 2 * v) := by
    intro θ
    have hk : ∀ k, loewnerLE (matrixLog (∫ ω, matrixExp (θ • X k ω) ∂μ))
        ((θ ^ 2 / 2) • A k ^ 2) := by
      intro k
      have e : (fun ω => matrixExp (θ • X k ω)) = fun ω => matrixExp ((θ * g k ω) • A k) := by
        funext ω
        simp only [X, smul_smul]
      rw [e]
      rcases hLaw with h | h
      · rw [(ch4_gaussian_mgf_cgf μ (A k) (hA k) (g k) (hMeas k) (h k) θ).2]
        show ((θ ^ 2 / 2) • A k ^ 2 - (θ ^ 2 / 2) • A k ^ 2).PosSemidef
        rw [sub_self]
        exact Matrix.PosSemidef.zero
      · exact (ch4_rademacher_mgf_cgf μ (A k) (hA k) (g k) (hMeas k) (h k) θ).2
    have hsum : loewnerLE (cumulantSum μ X θ) ((θ ^ 2 / 2) • ∑ k, A k ^ 2) := by
      unfold loewnerLE cumulantSum
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Matrix.posSemidef_sum _ (fun k _ => hk k)
    have hBH' : ((θ ^ 2 / 2) • ∑ k, A k ^ 2).IsHermitian :=
      hBherm.smul (isSelfAdjoint_iff.mpr (star_trivial _))
    calc traceExp (cumulantSum μ X θ) ≤ traceExp ((θ ^ 2 / 2) • ∑ k, A k ^ 2) :=
          ch8_trace_exp_monotone _ _ (hcumH θ) hBH' hsum
      _ ≤ d * Real.exp (θ ^ 2 / 2 * ‖∑ k, A k ^ 2‖) :=
          ch4hs_traceExp_le _ hBherm (by positivity)
      _ = d * Real.exp (θ ^ 2 / 2 * v) := by rw [hv]
  refine ⟨hv, ?_, ?_⟩
  · -- expectation bound
    have hE : ∀ θ : ℝ, 0 < θ → (∫ ω, lambdaMax (Y ω) ∂μ) ≤ Real.log d / θ + θ * v / 2 := by
      intro θ hθ
      have h1 := ((master_bounds μ X θ hXMeas hXHerm hXInt hXIndep (hXExp θ)).1 hθ).1
      have hpos : 0 < traceExp (cumulantSum μ X θ) := ch4hs_traceExp_pos _ (hcumH θ)
      have hlog : Real.log (traceExp (cumulantSum μ X θ)) ≤ Real.log d + θ ^ 2 / 2 * v := by
        calc _ ≤ Real.log (d * Real.exp (θ ^ 2 / 2 * v)) := Real.log_le_log hpos (hcgf θ)
          _ = _ := by rw [Real.log_mul hd0.ne' (Real.exp_pos _).ne', Real.log_exp]
      calc (∫ ω, lambdaMax (Y ω) ∂μ) ≤ Real.log (traceExp (cumulantSum μ X θ)) / θ := h1
        _ ≤ (Real.log d + θ ^ 2 / 2 * v) / θ := div_le_div_of_nonneg_right hlog hθ.le
        _ = Real.log d / θ + θ * v / 2 := by field_simp
    exact ch4hs_scalar (Real.log_nonneg hd) hv0 hE
  · -- tail bound
    have hT : ∀ θ : ℝ, 0 < θ → ∀ t : ℝ, (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
        d * Real.exp (-θ * t + θ ^ 2 / 2 * v) := by
      intro θ hθ t
      have h1 := ((master_bounds μ X θ hXMeas hXHerm hXInt hXIndep (hXExp θ)).1 hθ).2 t
      calc _ ≤ Real.exp (-θ * t) * traceExp (cumulantSum μ X θ) := h1
        _ ≤ Real.exp (-θ * t) * (d * Real.exp (θ ^ 2 / 2 * v)) :=
            mul_le_mul_of_nonneg_left (hcgf θ) (Real.exp_pos _).le
        _ = _ := by rw [Real.exp_add]; ring
    have hP1 : ∀ t : ℝ, (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤ d := fun t =>
      (measureReal_le_one (μ := μ)).trans hd
    intro t ht
    unfold gaussianSeriesTail
    split_ifs with hv0' ht0
    · exact hP1 t
    · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hlin : Tendsto (fun θ : ℝ => -θ * t) atTop atBot := by
        have := (tendsto_neg_atTop_atBot.comp (Filter.tendsto_id.atTop_mul_const htp))
        refine this.congr (fun θ => ?_)
        simp [neg_mul]
      have hlim : Tendsto (fun θ : ℝ => (d : ℝ) * Real.exp (-θ * t + θ ^ 2 / 2 * v)) atTop
          (𝓝 0) := by
        rw [hv0']
        simp only [mul_zero, add_zero]
        simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul (d : ℝ)
      exact ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun θ hθ => hT θ hθ t)
    · have hvp : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hv0')
      rcases ht.eq_or_lt with h0 | htp
      · subst h0
        simpa using hP1 0
      · have h := hT (t / v) (div_pos htp hvp) t
        have e : -(t / v) * t + (t / v) ^ 2 / 2 * v = -(t ^ 2) / (2 * v) := by
          field_simp
          ring
        rwa [e] at h
