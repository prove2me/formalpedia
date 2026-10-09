-- Prove2me | solution 1 for TroppMatrixConcentration.ch5_matrix_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:35:15.111477+00:00
-- url     : https://prove2.me/submissions/4060775d-e989-4a4f-9dc2-c58788069255

import Definitions.Def_TroppMatrixConcentration_ch5_chernoff_functions
import Theorems.Thm_TroppMatrixConcentration_master_bounds
import Theorems.Thm_TroppMatrixConcentration_ch5_chernoff_mgf_cgf
import Theorems.Thm_TroppMatrixConcentration_ch8_trace_exp_monotone
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option autoImplicit false

namespace TroppMatrixConcentration

lemma ch5mc_abs_le_norm {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ) {x : ℝ}
    (hx : x ∈ spectrum ℝ B) : |x| ≤ ‖B‖ := by
  have h : algebraMap ℝ ℂ x ∈ spectrum ℂ B := (spectrum.algebraMap_mem_iff ℂ).mpr hx
  have := spectrum.norm_le_norm_of_mem h
  simpa using this

lemma ch5mc_traceExp_eq_sum {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [traceExp, matrixExp, ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re]

lemma ch5mc_traceExp_pos {d : ℕ} [NeZero d] (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    0 < traceExp H := by
  have h := ch5mc_traceExp_eq_sum H hH 1
  rw [one_smul] at h
  rw [h]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

lemma ch5mc_mem_spec_bounds {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) {x : ℝ} (hx : x ∈ spectrum ℝ A) :
    lambdaMin A ≤ x ∧ x ≤ lambdaMax A := by
  have hf : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  exact ⟨csInf_le hf.bddBelow hx, le_csSup hf.bddAbove hx⟩

lemma ch5mc_eig_bounds {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (i : Fin d) :
    lambdaMin A ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ lambdaMax A :=
  ch5mc_mem_spec_bounds A hA (hA.eigenvalues_mem_spectrum_real i)

lemma ch5mc_norm_le {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) {L : ℝ} (hL : 0 ≤ L) (h0 : 0 ≤ lambdaMin A)
    (h1 : lambdaMax A ≤ L) : ‖A‖ ≤ L := by
  have h : ‖cfc (fun x : ℝ => x) A‖ ≤ L := by
    apply norm_cfc_le hL
    intro x hx
    obtain ⟨h2, h3⟩ := ch5mc_mem_spec_bounds A hA hx
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  rwa [cfc_id' ℝ A hA.isSelfAdjoint] at h

lemma ch5mc_traceExp_le_max {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) {c : ℝ} (hc : 0 ≤ c) :
    traceExp (c • B) ≤ d * Real.exp (c * lambdaMax B) := by
  rw [ch5mc_traceExp_eq_sum B hB c]
  calc ∑ i, Real.exp (c * hB.eigenvalues i) ≤ ∑ _i : Fin d, Real.exp (c * lambdaMax B) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ch5mc_eig_bounds B hB i).2 hc)
    _ = d * Real.exp (c * lambdaMax B) := by simp

lemma ch5mc_traceExp_le_min {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) {c : ℝ} (hc : c ≤ 0) :
    traceExp (c • B) ≤ d * Real.exp (c * lambdaMin B) := by
  rw [ch5mc_traceExp_eq_sum B hB c]
  calc ∑ i, Real.exp (c * hB.eigenvalues i) ≤ ∑ _i : Fin d, Real.exp (c * lambdaMin B) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (ch5mc_eig_bounds B hB i).1 hc)
    _ = d * Real.exp (c * lambdaMin B) := by simp

lemma ch5mc_norm_exp_le {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (s : ℝ) : ‖matrixExp (s • A)‖ ≤ Real.exp (|s| * ‖A‖) := by
  have hsA : (s • A).IsHermitian := hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hsA]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
  apply Real.exp_le_exp.mpr
  calc x ≤ |x| := le_abs_self x
    _ ≤ ‖s • A‖ := ch5mc_abs_le_norm _ hx
    _ = |s| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]

lemma ch5mc_lambda_zero {d : ℕ} [NeZero d] :
    lambdaMax (0 : Matrix (Fin d) (Fin d) ℂ) = 0 ∧ lambdaMin (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  unfold lambdaMax lambdaMin
  rw [spectrum.zero_eq]
  simp

lemma ch5mc_g_nonneg {L θ : ℝ} (hL : 0 ≤ L) (hθ : 0 ≤ θ) : 0 ≤ chernoffCgfCoefficient L θ := by
  unfold chernoffCgfCoefficient
  split_ifs with h
  · exact hθ
  · have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm h)
    apply div_nonneg _ hLp.le
    have : 1 ≤ Real.exp (θ * L) := Real.one_le_exp (mul_nonneg hθ hL)
    linarith

lemma ch5mc_g_nonpos {L θ : ℝ} (hL : 0 ≤ L) (hθ : θ ≤ 0) : chernoffCgfCoefficient L θ ≤ 0 := by
  unfold chernoffCgfCoefficient
  split_ifs with h
  · exact hθ
  · have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm h)
    apply div_nonpos_of_nonpos_of_nonneg _ hLp.le
    have : Real.exp (θ * L) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hθ hL)
    linarith

lemma ch5mc_g_pos {L θ : ℝ} (hL : 0 < L) :
    chernoffCgfCoefficient L θ = (Real.exp (θ * L) - 1) / L := by
  unfold chernoffCgfCoefficient
  rw [if_neg hL.ne']

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X k ω) ∧ lambdaMax (X k ω) ≤ L) :
    let Y := fun ω => ∑ k, X k ω
    let a := lambdaMin (∫ ω, Y ω ∂μ)
    let b := lambdaMax (∫ ω, Y ω ∂μ)
    a = lambdaMin (∑ k, ∫ ω, X k ω ∂μ) ∧
    b = lambdaMax (∑ k, ∫ ω, X k ω ∂μ) ∧
    (∀ θ : ℝ, 0 < θ →
      (1 - Real.exp (-θ)) / θ * a - L * Real.log d / θ ≤
        (∫ ω, lambdaMin (Y ω) ∂μ) ∧
      (∫ ω, lambdaMax (Y ω) ∂μ) ≤
        (Real.exp θ - 1) / θ * b + L * Real.log d / θ) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      (μ {ω | lambdaMin (Y ω) ≤ (1 - ε) * a}).toReal ≤
        chernoffLowerTail d a L ε) ∧
    (∀ ε : ℝ, 0 ≤ ε →
      (μ {ω | (1 + ε) * b ≤ lambdaMax (Y ω)}).toReal ≤
        chernoffUpperTail d b L ε) := by
  intro Y a b
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le one_pos hd
  have hnorm : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ L := fun k => by
    filter_upwards [hHerm k, hBound k] with ω h1 h2
    exact ch5mc_norm_le _ h1 hL h2.1 h2.2
  have hInt : ∀ k, Integrable (X k) μ := fun k =>
    Integrable.of_bound (hMeas k).aestronglyMeasurable L (hnorm k)
  have hExp : ∀ θ : ℝ, ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ := by
    intro θ k
    let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ _
    refine Integrable.of_bound ?_ (Real.exp (|θ| * L)) ?_
    · have hcont : Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (θ • A)) :=
        NormedSpace.exp_continuous.comp (continuous_const_smul θ)
      exact hcont.comp_aestronglyMeasurable (hMeas k).aestronglyMeasurable
    · filter_upwards [hHerm k, hnorm k] with ω h1 h2
      exact (ch5mc_norm_exp_le _ h1 θ).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2 (abs_nonneg θ)))
  obtain ⟨B, hBdef⟩ : ∃ B, B = ∑ k, ∫ ω, X k ω ∂μ := ⟨_, rfl⟩
  have hYB : ∫ ω, Y ω ∂μ = B := by
    rw [hBdef]
    exact integral_finsetSum _ (fun k _ => hInt k)
  have ha : a = lambdaMin B := by
    show lambdaMin (∫ ω, Y ω ∂μ) = _
    rw [hYB]
  have hb : b = lambdaMax B := by
    show lambdaMax (∫ ω, Y ω ∂μ) = _
    rw [hYB]
  -- Hermiticity of the mean
  have hXnonneg : ∀ k, ∀ᵐ ω ∂μ, (0 : Matrix (Fin d) (Fin d) ℂ) ≤ X k ω := by
    intro k
    filter_upwards [hHerm k, hBound k] with ω h1 h2
    apply Matrix.PosSemidef.nonneg
    rw [h1.posSemidef_iff_eigenvalues_nonneg]
    intro i
    exact h2.1.trans (ch5mc_eig_bounds _ h1 i).1
  have hBH : B.IsHermitian := by
    rw [hBdef]
    exact isSelfAdjoint_sum _ (fun k _ =>
      (Matrix.nonneg_iff_posSemidef.mp (integral_nonneg_of_ae (hXnonneg k))).isHermitian)
  -- cumulant bounds
  have hcumH : ∀ θ : ℝ, (cumulantSum μ X θ).IsHermitian := fun θ =>
    isSelfAdjoint_sum _ (fun k _ => by unfold matrixLog; exact IsSelfAdjoint.cfc)
  have hcum : ∀ θ : ℝ, traceExp (cumulantSum μ X θ) ≤
      traceExp (chernoffCgfCoefficient L θ • B) := by
    intro θ
    have hk := fun k => (ch5_chernoff_mgf_cgf μ (X k) L hL (hMeas k) (hHerm k) (hBound k) θ).2
    have hsum : loewnerLE (cumulantSum μ X θ) (chernoffCgfCoefficient L θ • B) := by
      unfold loewnerLE cumulantSum
      rw [hBdef, Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Matrix.posSemidef_sum _ (fun k _ => hk k)
    exact ch8_trace_exp_monotone _ _ (hcumH θ)
      (hBH.smul (isSelfAdjoint_iff.mpr (star_trivial _))) hsum
  have htrU : ∀ θ : ℝ, 0 ≤ θ → traceExp (cumulantSum μ X θ) ≤
      d * Real.exp (chernoffCgfCoefficient L θ * lambdaMax B) := fun θ hθ =>
    (hcum θ).trans (ch5mc_traceExp_le_max B hBH (ch5mc_g_nonneg hL hθ))
  have htrL : ∀ θ : ℝ, θ ≤ 0 → traceExp (cumulantSum μ X θ) ≤
      d * Real.exp (chernoffCgfCoefficient L θ * lambdaMin B) := fun θ hθ =>
    (hcum θ).trans (ch5mc_traceExp_le_min B hBH (ch5mc_g_nonpos hL hθ))
  have hlog : ∀ θ c : ℝ, traceExp (cumulantSum μ X θ) ≤ d * Real.exp c →
      Real.log (traceExp (cumulantSum μ X θ)) ≤ Real.log d + c := by
    intro θ c h
    calc _ ≤ Real.log (d * Real.exp c) := Real.log_le_log (ch5mc_traceExp_pos _ (hcumH θ)) h
      _ = _ := by rw [Real.log_mul hd0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hP1 : ∀ s : Set Ω, (μ s).toReal ≤ d := fun s =>
    (measureReal_le_one (μ := μ)).trans hd
  have hYdef : ∀ ω, Y ω = ∑ k, X k ω := fun ω => rfl
  clear_value Y a b
  subst ha hb
  refine ⟨by rw [hBdef], by rw [hBdef], ?_, ?_, ?_⟩
  · -- expectation bounds
    intro θ hθ
    rcases hL.eq_or_lt with hL0 | hLp
    · -- L = 0: everything vanishes
      subst hL0
      have hX0 : ∀ᵐ ω ∂μ, ∀ k, X k ω = 0 := by
        rw [ae_all_iff]
        intro k
        filter_upwards [hnorm k] with ω h
        exact norm_le_zero_iff.mp h
      have hB0 : B = 0 := by
        rw [hBdef]
        apply Finset.sum_eq_zero
        intro k _
        rw [integral_congr_ae (hX0.mono fun ω h => h k)]
        simp
      have hmin : ∫ ω, lambdaMin (Y ω) ∂μ = 0 := by
        rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
        · simp
        · filter_upwards [hX0] with ω h
          simp [hYdef, h, ch5mc_lambda_zero]
      have hmax : ∫ ω, lambdaMax (Y ω) ∂μ = 0 := by
        rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
        · simp
        · filter_upwards [hX0] with ω h
          simp [hYdef, h, ch5mc_lambda_zero]
      rw [hmin, hmax, hB0, ch5mc_lambda_zero.1, ch5mc_lambda_zero.2]
      simp
    · constructor
      · have hθ' : -θ / L < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr hθ) hLp
        have h1 := ((master_bounds μ X (-θ / L) hMeas hHerm hInt hIndep (hExp _)).2 hθ').1
        have h2 := hlog _ _ (htrL _ hθ'.le)
        have h3 := div_le_div_of_nonpos_of_le hθ'.le h2
        have e : (Real.log d + chernoffCgfCoefficient L (-θ / L) * lambdaMin B) / (-θ / L) =
            (1 - Real.exp (-θ)) / θ * lambdaMin B - L * Real.log d / θ := by
          rw [ch5mc_g_pos hLp, div_mul_cancel₀ _ hLp.ne']
          field_simp
          ring
        rw [e] at h3
        simp only [hYdef]
        linarith
      · have hθ' : 0 < θ / L := div_pos hθ hLp
        have h1 := ((master_bounds μ X (θ / L) hMeas hHerm hInt hIndep (hExp _)).1 hθ').1
        have h2 := hlog _ _ (htrU _ hθ'.le)
        have h3 := div_le_div_of_nonneg_right h2 hθ'.le
        have e : (Real.log d + chernoffCgfCoefficient L (θ / L) * lambdaMax B) / (θ / L) =
            (Real.exp θ - 1) / θ * lambdaMax B + L * Real.log d / θ := by
          rw [ch5mc_g_pos hLp, div_mul_cancel₀ _ hLp.ne']
          field_simp
          ring
        rw [e] at h3
        simp only [hYdef]
        linarith
  · -- lower tail
    intro ε hε0 hε1
    rcases hL.eq_or_lt with hL0 | hLp
    · unfold chernoffLowerTail
      rw [if_pos hL0.symm]
      exact hP1 _
    rcases hε0.eq_or_lt with hε | hεp
    · subst hε
      unfold chernoffLowerTail
      rw [if_neg hLp.ne']
      simpa using hP1 _
    have h1e : 0 < 1 - ε := by linarith
    have hθ' : Real.log (1 - ε) / L < 0 :=
      div_neg_of_neg_of_pos (Real.log_neg h1e (by linarith)) hLp
    have h1 := ((master_bounds μ X _ hMeas hHerm hInt hIndep (hExp _)).2 hθ').2
      ((1 - ε) * lambdaMin B)
    have h2 := htrL _ hθ'.le
    rw [ch5mc_g_pos hLp, div_mul_cancel₀ _ hLp.ne', Real.exp_log h1e] at h2
    unfold chernoffLowerTail
    rw [if_neg hLp.ne']
    have hbase : 0 < Real.exp (-ε) / Real.rpow (1 - ε) (1 - ε) :=
      div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos h1e _)
    have e : Real.rpow (Real.exp (-ε) / Real.rpow (1 - ε) (1 - ε)) (lambdaMin B / L) =
        Real.exp (-(Real.log (1 - ε) / L) * ((1 - ε) * lambdaMin B) +
          (1 - ε - 1) / L * lambdaMin B) := by
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hbase, Real.rpow_eq_pow,
        Real.log_div (Real.exp_pos _).ne' (Real.rpow_pos_of_pos h1e _).ne',
        Real.log_exp, Real.log_rpow h1e]
      congr 1
      field_simp
      ring
    rw [e, Real.exp_add]
    simp only [hYdef]
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by ring
  · -- upper tail
    intro ε hε0
    rcases hL.eq_or_lt with hL0 | hLp
    · unfold chernoffUpperTail
      rw [if_pos hL0.symm]
      exact hP1 _
    rcases hε0.eq_or_lt with hε | hεp
    · subst hε
      unfold chernoffUpperTail
      rw [if_neg hLp.ne']
      simpa using hP1 _
    have h1e : 0 < 1 + ε := by linarith
    have hθ' : 0 < Real.log (1 + ε) / L :=
      div_pos (Real.log_pos (by linarith)) hLp
    have h1 := ((master_bounds μ X _ hMeas hHerm hInt hIndep (hExp _)).1 hθ').2
      ((1 + ε) * lambdaMax B)
    have h2 := htrU _ hθ'.le
    rw [ch5mc_g_pos hLp, div_mul_cancel₀ _ hLp.ne', Real.exp_log h1e] at h2
    unfold chernoffUpperTail
    rw [if_neg hLp.ne']
    have hbase : 0 < Real.exp ε / Real.rpow (1 + ε) (1 + ε) :=
      div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos h1e _)
    have e : Real.rpow (Real.exp ε / Real.rpow (1 + ε) (1 + ε)) (lambdaMax B / L) =
        Real.exp (-(Real.log (1 + ε) / L) * ((1 + ε) * lambdaMax B) +
          (1 + ε - 1) / L * lambdaMax B) := by
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hbase, Real.rpow_eq_pow,
        Real.log_div (Real.exp_pos _).ne' (Real.rpow_pos_of_pos h1e _).ne',
        Real.log_exp, Real.log_rpow h1e]
      congr 1
      field_simp
      ring
    rw [e, Real.exp_add]
    simp only [hYdef]
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by ring
