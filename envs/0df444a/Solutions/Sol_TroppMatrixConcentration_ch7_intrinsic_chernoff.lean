-- Prove2me | solution 1 for TroppMatrixConcentration.ch7_intrinsic_chernoff
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:41:42.775815+00:00
-- url     : https://prove2.me/submissions/ac62b7a2-6dfa-4f29-b39e-7397d91d5263

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic
import Definitions.Def_TroppMatrixConcentration_ch5_chernoff_functions
import Theorems.Thm_TroppMatrixConcentration_ch7_generalized_laplace
import Theorems.Thm_TroppMatrixConcentration_ch7_intrinsic_dimension
import Theorems.Thm_TroppMatrixConcentration_ch5_chernoff_mgf_cgf
import Theorems.Thm_TroppMatrixConcentration_trace_cgf_subadditivity
import Theorems.Thm_TroppMatrixConcentration_ch8_trace_exp_monotone
import Theorems.Thm_TroppMatrixConcentration_ch3_lieb_jensen
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TroppMatrixConcentration

lemma icher_traceFunction_eq_sum {d : ℕ} (φ : ℝ → ℝ)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    traceFunction φ A = ∑ i, φ (hA.eigenvalues i) := by
  rw [traceFunction, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp

lemma icher_traceExp_eq_sum {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [traceExp, matrixExp,
    ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re]

lemma icher_abs_le_norm {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ) {x : ℝ}
    (hx : x ∈ spectrum ℝ B) : |x| ≤ ‖B‖ := by
  have h : algebraMap ℝ ℂ x ∈ spectrum ℂ B := (spectrum.algebraMap_mem_iff ℂ).mpr hx
  have := spectrum.norm_le_norm_of_mem h
  simpa using this

lemma icher_lambdaMax_mem {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) : ∃ i, hB.eigenvalues i = lambdaMax B := by
  have hn : (Set.range hB.eigenvalues).Nonempty := Set.range_nonempty _
  have hf : (Set.range hB.eigenvalues).Finite := Set.finite_range _
  have hmax : lambdaMax B ∈ Set.range hB.eigenvalues := by
    simpa only [lambdaMax, hB.spectrum_real_eq_range_eigenvalues] using hn.csSup_mem hf
  exact hmax

lemma icher_eig_le_lambdaMax {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) (i : Fin d) : hB.eigenvalues i ≤ lambdaMax B := by
  unfold lambdaMax
  rw [hB.spectrum_real_eq_range_eigenvalues]
  exact le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)

/-- For a PSD matrix, the maximum eigenvalue equals the spectral norm. -/
lemma icher_lambdaMax_eq_norm {d : ℕ} [NeZero d] (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.PosSemidef) : lambdaMax P = ‖P‖ := by
  have hA := hP.isHermitian
  apply le_antisymm
  · obtain ⟨i, hi⟩ := icher_lambdaMax_mem P hA
    rw [← hi]
    exact (le_abs_self _).trans (icher_abs_le_norm P (hA.eigenvalues_mem_spectrum_real i))
  · have hbdd : BddAbove (spectrum ℝ P) := by
      rw [hA.spectrum_real_eq_range_eigenvalues]; exact (Set.finite_range _).bddAbove
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (hA : IsSelfAdjoint P) with h | h
    · exact le_csSup hbdd h
    · have h1 : -‖P‖ ≤ lambdaMax P := le_csSup hbdd h
      rw [hA.spectrum_real_eq_range_eigenvalues] at h
      obtain ⟨i, hi⟩ := h
      have h2 := hP.eigenvalues_nonneg i
      rw [hi] at h2
      have h3 : ‖P‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
      rw [h3] at h1 ⊢
      linarith

lemma icher_lambdaMin_nonneg {d : ℕ} [NeZero d] (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.PosSemidef) : 0 ≤ lambdaMin P := by
  unfold lambdaMin
  rw [hP.isHermitian.spectrum_real_eq_range_eigenvalues]
  exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact hP.eigenvalues_nonneg i)

lemma icher_intrinsic_ge_one {d : ℕ} [NeZero d] (M : Matrix (Fin d) (Fin d) ℂ)
    (hP : M.PosSemidef) (hM : M ≠ 0) : 1 ≤ intrinsicDimension M := by
  have hA := hP.isHermitian
  have htr : (Matrix.trace M).re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]; simp
  have hn : 0 < ‖M‖ := norm_pos_iff.mpr hM
  obtain ⟨i, hi⟩ := icher_lambdaMax_mem M hA
  have hle : ‖M‖ ≤ ∑ j, hA.eigenvalues j := by
    rw [← icher_lambdaMax_eq_norm M hP, ← hi]
    exact Finset.single_le_sum (fun j _ => hP.eigenvalues_nonneg j) (Finset.mem_univ i)
  unfold intrinsicDimension spectralNorm
  rw [htr, le_div_iff₀ hn, one_mul]
  exact hle

lemma icher_W_facts {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ)
    (hP : B.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ traceExp (c • B) - d ∧ Real.exp (c * lambdaMax B) - 1 ≤ traceExp (c • B) - d := by
  have hA := hP.isHermitian
  have e : traceExp (c • B) - d = ∑ i, (Real.exp (c * hA.eigenvalues i) - 1) := by
    rw [icher_traceExp_eq_sum B hA c, Finset.sum_sub_distrib]; simp
  have hnn : ∀ i, 0 ≤ Real.exp (c * hA.eigenvalues i) - 1 := fun i => by
    have := Real.one_le_exp (mul_nonneg hc (hP.eigenvalues_nonneg i)); linarith
  rw [e]
  refine ⟨Finset.sum_nonneg (fun i _ => hnn i), ?_⟩
  obtain ⟨i, hi⟩ := icher_lambdaMax_mem B hA
  rw [← hi]
  exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)

lemma icher_traceFunction_psi {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ)
    (hP : B.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    traceFunction (fun x => max 0 (Real.exp (c * x) - 1)) B = traceExp (c • B) - d := by
  have hA := hP.isHermitian
  rw [icher_traceFunction_eq_sum _ B hA, icher_traceExp_eq_sum B hA c]
  rw [Finset.sum_congr rfl (fun i _ => max_eq_right
    (sub_nonneg.2 (Real.one_le_exp (mul_nonneg hc (hP.eigenvalues_nonneg i)))))]
  rw [Finset.sum_sub_distrib]; simp

lemma icher_traceFunction_expm1 {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ)
    (hA : B.IsHermitian) (c : ℝ) :
    traceFunction (fun x => Real.exp (c * x) - 1) B = traceExp (c • B) - d := by
  rw [icher_traceFunction_eq_sum _ B hA, icher_traceExp_eq_sum B hA c, Finset.sum_sub_distrib]
  simp

lemma icher_norm_exp_le {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (s : ℝ) : ‖matrixExp (s • A)‖ ≤ Real.exp (|s| * ‖A‖) := by
  have hsA : (s • A).IsHermitian := hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hsA]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
  apply Real.exp_le_exp.mpr
  calc x ≤ |x| := le_abs_self x
    _ ≤ ‖s • A‖ := icher_abs_le_norm _ hx
    _ = |s| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]

lemma icher_expm1_convex (g : ℝ) :
    ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => Real.exp (g * x) - 1) := by
  refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
  have h := convexOn_exp.2 (Set.mem_univ (g * x)) (Set.mem_univ (g * y)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have e : g * (a * x + b * y) = a * (g * x) + b * (g * y) := by ring
  rw [e]
  calc Real.exp (a * (g * x) + b * (g * y)) - 1
      ≤ a * Real.exp (g * x) + b * Real.exp (g * y) - 1 := by linarith
    _ = a * (Real.exp (g * x) - 1) + b * (Real.exp (g * y) - 1) := by linear_combination hab

lemma icher_log1p_concave :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun u : ℝ => Real.log (1 + u)) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : (1 + x) ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]; simp only [Set.mem_Ici] at hx; linarith
  have hy' : (1 + y) ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]; simp only [Set.mem_Ici] at hy; linarith
  have h := strictConcaveOn_log_Ioi.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have e : a * (1 + x) + b * (1 + y) = 1 + (a * x + b * y) := by linear_combination hab
  rw [e] at h
  exact h

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ)
    (L : ℝ) (hL : 0 < L) (M : Matrix (Fin d) (Fin d) ℂ) (hM : M ≠ 0)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hPSD : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (X k ω) ≤ L)
    (hMeanBound : loewnerLE (∫ ω, ∑ k, X k ω ∂μ) M) :
    let Y := fun ω => ∑ k, X k ω
    let r := intrinsicDimension M
    let a := lambdaMax M
    (∫ ω, Y ω ∂μ) = ∑ k, ∫ ω, X k ω ∂μ ∧
    (∀ θ : ℝ, 0 < θ → (∫ ω, lambdaMax (Y ω) ∂μ) ≤
      (Real.exp θ - 1) / θ * a + L / θ * Real.log (2 * r)) ∧
    ∀ ε : ℝ, L / a ≤ ε →
      (μ {ω | (1 + ε) * a ≤ lambdaMax (Y ω)}).toReal ≤
        2 * r * Real.exp (a / L * (ε - (1 + ε) * Real.log (1 + ε))) := by
  intro Y r a
  -- preliminaries
  have hXnorm : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ L := fun k => by
    filter_upwards [hPSD k, hBound k] with ω h1 h2
    rw [← icher_lambdaMax_eq_norm _ h1]; exact h2
  have hXInt : ∀ k, Integrable (X k) μ := fun k =>
    Integrable.of_bound (hMeas k).aestronglyMeasurable L (hXnorm k)
  have hXHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian := fun k =>
    (hPSD k).mono fun ω h => h.isHermitian
  have hYMeas : Measurable Y := Finset.measurable_sum _ (fun k _ => hMeas k)
  have hYPSD : ∀ᵐ ω ∂μ, (Y ω).PosSemidef := by
    filter_upwards [ae_all_iff.2 hPSD] with ω h
    exact Matrix.posSemidef_sum _ (fun k _ => h k)
  have hYnorm : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ N * L := by
    filter_upwards [ae_all_iff.2 hXnorm] with ω h
    calc ‖Y ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin N, L := Finset.sum_le_sum (fun k _ => h k)
      _ = N * L := by simp
  have hInt1 : (∫ ω, Y ω ∂μ) = ∑ k, ∫ ω, X k ω ∂μ :=
    integral_finsetSum _ (fun k _ => hXInt k)
  have hIntPSD : (∫ ω, Y ω ∂μ).PosSemidef := by
    have h0 : ∀ᵐ ω ∂μ, (0 : Matrix (Fin d) (Fin d) ℂ) ≤ Y ω :=
      hYPSD.mono fun ω h => Matrix.nonneg_iff_posSemidef.mpr h
    exact Matrix.nonneg_iff_posSemidef.mp (integral_nonneg_of_ae h0)
  have hMPSD : M.PosSemidef := by
    have h := hMeanBound.add hIntPSD
    rwa [sub_add_cancel] at h
  have ha : a = ‖M‖ := icher_lambdaMax_eq_norm M hMPSD
  have hapos : 0 < a := ha ▸ norm_pos_iff.mpr hM
  have hr1 : 1 ≤ r := icher_intrinsic_ge_one M hMPSD hM
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  -- continuity of traceExp
  let _ : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hcontExp : ∀ c : ℝ, Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (c • A)) := by
    intro c
    dsimp [matrixExp]
    fun_prop
  have hcontTr : ∀ c : ℝ, Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => traceExp (c • A)) := by
    intro c
    unfold traceExp
    exact Complex.continuous_re.comp ((continuous_id.matrix_trace).comp (hcontExp c))
  -- the expected trace bound
  have key : ∀ θ' : ℝ, 0 < θ' →
      Integrable (fun ω => traceExp (θ' • Y ω) - d) μ ∧
      (∫ ω, (traceExp (θ' • Y ω) - d) ∂μ) ≤
        r * Real.exp (chernoffCgfCoefficient L θ' * a) := by
    intro θ' hθ'
    set g := chernoffCgfCoefficient L θ' with hg_def
    have hg : g = (Real.exp (θ' * L) - 1) / L := by
      rw [hg_def, chernoffCgfCoefficient, if_neg hL.ne']
    have hg0 : 0 ≤ g := by
      rw [hg]
      exact div_nonneg (sub_nonneg.2 (Real.one_le_exp (mul_nonneg hθ'.le hL.le))) hL.le
    have hTInt : Integrable (fun ω => traceExp (θ' • Y ω)) μ := by
      refine Integrable.of_bound ((hcontTr θ').comp_aestronglyMeasurable
        hYMeas.aestronglyMeasurable) (d * Real.exp (θ' * (N * L))) ?_
      filter_upwards [hYPSD, hYnorm] with ω h1 h2
      have hnn : 0 ≤ traceExp (θ' • Y ω) := by
        have := (icher_W_facts _ h1 hθ'.le).1; have : (0:ℝ) ≤ d := by positivity
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, icher_traceExp_eq_sum _ h1.isHermitian]
      calc ∑ i, Real.exp (θ' * h1.isHermitian.eigenvalues i)
          ≤ ∑ _i : Fin d, Real.exp (θ' * (N * L)) := by
            apply Finset.sum_le_sum
            intro i _
            apply Real.exp_le_exp.mpr
            apply mul_le_mul_of_nonneg_left _ hθ'.le
            exact ((le_abs_self _).trans (icher_abs_le_norm _
              (h1.isHermitian.eigenvalues_mem_spectrum_real i))).trans h2
        _ = d * Real.exp (θ' * (N * L)) := by simp
    have hWInt : Integrable (fun ω => traceExp (θ' • Y ω) - d) μ :=
      hTInt.sub (integrable_const _)
    refine ⟨hWInt, ?_⟩
    have hExp : ∀ k, Integrable (fun ω => matrixExp (θ' • X k ω)) μ := by
      intro k
      refine Integrable.of_bound ((hcontExp θ').comp_aestronglyMeasurable
        (hMeas k).aestronglyMeasurable) (Real.exp (|θ'| * L)) ?_
      filter_upwards [hXHerm k, hXnorm k] with ω h1 h2
      exact (icher_norm_exp_le _ h1 θ').trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
    have hsub := trace_cgf_subadditivity μ X θ' hMeas hXHerm hIndep hExp
    have e1 : (fun ω => traceExp (∑ k, θ' • X k ω)) = fun ω => traceExp (θ' • Y ω) := by
      funext ω
      simp only [Y, Finset.smul_sum]
    rw [e1] at hsub
    have hk : ∀ k, loewnerLE (matrixLog (∫ ω, matrixExp (θ' • X k ω) ∂μ))
        (g • ∫ ω, X k ω ∂μ) := by
      intro k
      have hb : ∀ᵐ ω ∂μ, 0 ≤ lambdaMin (X k ω) ∧ lambdaMax (X k ω) ≤ L := by
        filter_upwards [hPSD k, hBound k] with ω h1 h2
        exact ⟨icher_lambdaMin_nonneg _ h1, h2⟩
      exact (ch5_chernoff_mgf_cgf μ (X k) L hL.le (hMeas k) (hXHerm k) hb θ').2
    have hsum : loewnerLE (cumulantSum μ X θ') (g • ∑ k, ∫ ω, X k ω ∂μ) := by
      unfold loewnerLE cumulantSum
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Matrix.posSemidef_sum _ (fun k _ => hk k)
    rw [← hInt1] at hsum
    have hcumH : (cumulantSum μ X θ').IsHermitian :=
      isSelfAdjoint_sum _ (fun k _ => by unfold matrixLog; exact IsSelfAdjoint.cfc)
    have hgYH : (g • ∫ ω, Y ω ∂μ).IsHermitian :=
      hIntPSD.isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial _))
    have hgMH : (g • M).IsHermitian :=
      hMPSD.isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial _))
    have hle2 : loewnerLE (g • ∫ ω, Y ω ∂μ) (g • M) := by
      unfold loewnerLE
      rw [← smul_sub]
      exact Matrix.PosSemidef.smul hMeanBound hg0
    have hT : (∫ ω, traceExp (θ' • Y ω) ∂μ) ≤ traceExp (g • M) :=
      hsub.trans ((ch8_trace_exp_monotone _ _ hcumH hgYH hsum).trans
        (ch8_trace_exp_monotone _ _ hgYH hgMH hle2))
    have hID := ch7_intrinsic_dimension (fun x => Real.exp (g * x) - 1)
      (icher_expm1_convex g) (by simp) M hMPSD
    rw [icher_traceFunction_expm1 M hMPSD.isHermitian g] at hID
    have hE : (∫ ω, (traceExp (θ' • Y ω) - d) ∂μ) = (∫ ω, traceExp (θ' • Y ω) ∂μ) - d := by
      rw [integral_sub hTInt (integrable_const _)]
      simp
    rw [hE]
    calc (∫ ω, traceExp (θ' • Y ω) ∂μ) - d ≤ traceExp (g • M) - d := by linarith
      _ ≤ r * (Real.exp (g * a) - 1) := by
        have : spectralNorm M = a := ha.symm
        rw [this] at hID
        exact hID
      _ ≤ r * Real.exp (g * a) := by nlinarith
  refine ⟨hInt1, ?_, ?_⟩
  · -- expectation bound
    intro θ hθ
    set θ' := θ / L with hθ'_def
    have hθ' : 0 < θ' := div_pos hθ hL
    obtain ⟨hWInt, hWle⟩ := key θ' hθ'
    set g := chernoffCgfCoefficient L θ' with hg_def
    have hg : g = (Real.exp θ - 1) / L := by
      rw [hg_def, chernoffCgfCoefficient, if_neg hL.ne', hθ'_def, div_mul_cancel₀ θ hL.ne']
    have hg0 : 0 ≤ g := by
      rw [hg]; exact div_nonneg (sub_nonneg.2 (Real.one_le_exp hθ.le)) hL.le
    set W := fun ω => traceExp (θ' • Y ω) - d with hW_def
    have hW0 : ∀ᵐ ω ∂μ, 0 ≤ W ω := hYPSD.mono fun ω h => (icher_W_facts _ h hθ'.le).1
    have hlogInt : Integrable (fun ω => Real.log (1 + W ω)) μ := by
      refine hWInt.mono' ?_ ?_
      · exact (Real.measurable_log.comp_aemeasurable
          (hWInt.aemeasurable.const_add 1)).aestronglyMeasurable
      · filter_upwards [hW0] with ω h
        have h1 : 0 ≤ Real.log (1 + W ω) := Real.log_nonneg (by linarith)
        have h2 := Real.log_le_sub_one_of_pos (show 0 < 1 + W ω by linarith)
        rw [Real.norm_eq_abs, abs_of_nonneg h1]
        linarith
    have hpt : ∀ᵐ ω ∂μ, lambdaMax (Y ω) ≤ Real.log (1 + W ω) / θ' := by
      filter_upwards [hYPSD] with ω h
      have h1 := (icher_W_facts _ h hθ'.le).2
      have h2 : Real.exp (θ' * lambdaMax (Y ω)) ≤ 1 + W ω := by
        simp only [hW_def]; linarith
      have h3 := Real.log_le_log (Real.exp_pos _) h2
      rw [Real.log_exp] at h3
      rw [le_div_iff₀ hθ']
      linarith
    have hnn : ∀ᵐ ω ∂μ, 0 ≤ lambdaMax (Y ω) := by
      filter_upwards [hYPSD] with ω h
      rw [icher_lambdaMax_eq_norm _ h]; exact norm_nonneg _
    have hstep1 : (∫ ω, lambdaMax (Y ω) ∂μ) ≤ ∫ ω, Real.log (1 + W ω) / θ' ∂μ :=
      integral_mono_of_nonneg hnn (hlogInt.div_const θ') hpt
    rw [integral_div] at hstep1
    have hcont : ContinuousOn (fun u : ℝ => Real.log (1 + u)) (Set.Ici 0) := by
      apply ContinuousOn.log (continuousOn_const.add continuousOn_id)
      intro x hx
      have h0 : (0 : ℝ) < 1 + x := by simp only [Set.mem_Ici] at hx; linarith
      exact h0.ne'
    have hm : (∫ ω, W ω ∂μ) ∈ Set.Ici (0 : ℝ) := integral_nonneg_of_ae hW0
    have hJ := ch3_lieb_jensen μ (Set.Ici (0 : ℝ)) (fun u => Real.log (1 + u)) W
      icher_log1p_concave hcont hW0 hWInt hlogInt hm
    have hEa : 0 ≤ g * a := mul_nonneg hg0 hapos.le
    have h1 : 1 ≤ r * Real.exp (g * a) := by
      have := Real.one_le_exp hEa
      nlinarith
    have hm' : 0 ≤ ∫ ω, W ω ∂μ := hm
    have hlog2 : Real.log (1 + ∫ ω, W ω ∂μ) ≤ Real.log (2 * r) + g * a := by
      calc Real.log (1 + ∫ ω, W ω ∂μ) ≤ Real.log (2 * r * Real.exp (g * a)) := by
            apply Real.log_le_log (by linarith)
            have : (∫ ω, W ω ∂μ) ≤ r * Real.exp (g * a) := hWle
            linarith
        _ = Real.log (2 * r) + g * a := by
            rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    calc (∫ ω, lambdaMax (Y ω) ∂μ) ≤ (∫ ω, Real.log (1 + W ω) ∂μ) / θ' := hstep1
      _ ≤ Real.log (1 + ∫ ω, W ω ∂μ) / θ' := div_le_div_of_nonneg_right hJ hθ'.le
      _ ≤ (Real.log (2 * r) + g * a) / θ' := div_le_div_of_nonneg_right hlog2 hθ'.le
      _ = (Real.exp θ - 1) / θ * a + L / θ * Real.log (2 * r) := by
          rw [hg, hθ'_def]
          field_simp
          ring
  · -- tail bound
    intro ε hε
    have hεa : L ≤ ε * a := by rwa [div_le_iff₀ hapos] at hε
    have hε0 : 0 < ε := by
      by_contra h
      push Not at h
      nlinarith
    have h1ε : 0 < 1 + ε := by linarith
    set θ' := Real.log (1 + ε) / L with hθ'_def
    have hθ' : 0 < θ' := div_pos (Real.log_pos (by linarith)) hL
    obtain ⟨hWInt, hWle⟩ := key θ' hθ'
    have hg : chernoffCgfCoefficient L θ' = ε / L := by
      rw [chernoffCgfCoefficient, if_neg hL.ne', hθ'_def, div_mul_cancel₀ _ hL.ne',
        Real.exp_log h1ε]
      ring
    rw [hg] at hWle
    set t := (1 + ε) * a with ht_def
    have ht : 0 ≤ t := by positivity
    set ψ : ℝ → ℝ := fun x => max 0 (Real.exp (θ' * x) - 1) with hψ_def
    have hψnn : ∀ x, 0 ≤ ψ x := fun x => le_max_left _ _
    have hψmono : MonotoneOn ψ (Set.Ici 0) := by
      intro x _ y _ hxy
      exact max_le_max le_rfl (sub_le_sub_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hθ'.le)) 1)
    have hψY : ∀ᵐ ω ∂μ, traceFunction ψ (Y ω) = traceExp (θ' • Y ω) - d := by
      filter_upwards [hYPSD] with ω h
      exact icher_traceFunction_psi _ h hθ'.le
    have hψInt : Integrable (fun ω => traceFunction ψ (Y ω)) μ :=
      hWInt.congr (hψY.mono fun ω h => h.symm)
    -- s = θ' t ≥ 1
    have hlogε : ε ≤ (1 + ε) * Real.log (1 + ε) := by
      have h := Real.add_one_le_exp (-Real.log (1 + ε))
      rw [Real.exp_neg, Real.exp_log h1ε] at h
      have h2 : (1 + ε) * (-Real.log (1 + ε) + 1) ≤ (1 + ε) * (1 + ε)⁻¹ :=
        mul_le_mul_of_nonneg_left h h1ε.le
      rw [mul_inv_cancel₀ h1ε.ne'] at h2
      linarith
    have hs1 : 1 ≤ θ' * t := by
      have e : θ' * t = ((1 + ε) * Real.log (1 + ε)) * a / L := by
        rw [hθ'_def, ht_def]; ring
      rw [e, le_div_iff₀ hL, one_mul]
      exact hεa.trans (mul_le_mul_of_nonneg_right hlogε hapos.le)
    have hX2 : 2 ≤ Real.exp (θ' * t) := by
      have := Real.add_one_le_exp (θ' * t); linarith
    have hψt : ψ t = Real.exp (θ' * t) - 1 := max_eq_right (by linarith)
    have hψtpos : 0 < ψ t := by rw [hψt]; linarith
    have hlap := ch7_generalized_laplace μ Y ψ hYMeas (hYPSD.mono fun ω h => h.isHermitian)
      hψnn hψmono hψInt t ht hψtpos
    rw [integral_congr_ae hψY, hψt] at hlap
    have hEpos : 0 ≤ Real.exp (ε / L * a) := (Real.exp_pos _).le
    set E := Real.exp (ε / L * a) with hE_def
    set Xs := Real.exp (θ' * t) with hXs_def
    have hXpos : 0 < Xs := by linarith
    calc (μ {ω | (1 + ε) * a ≤ lambdaMax (Y ω)}).toReal
        ≤ (∫ ω, (traceExp (θ' • Y ω) - d) ∂μ) / (Xs - 1) := hlap
      _ ≤ r * E / (Xs - 1) := div_le_div_of_nonneg_right hWle (by linarith)
      _ ≤ 2 * r * (E / Xs) := by
          rw [div_le_iff₀ (by linarith), show 2 * r * (E / Xs) * (Xs - 1)
            = (2 * r * E * (Xs - 1)) / Xs by ring, le_div_iff₀ hXpos]
          have := mul_nonneg (mul_nonneg hr0 hEpos) (sub_nonneg.2 hX2)
          nlinarith
      _ = 2 * r * Real.exp (a / L * (ε - (1 + ε) * Real.log (1 + ε))) := by
          rw [hE_def, hXs_def, ← Real.exp_sub]
          congr 2
          rw [hθ'_def, ht_def]
          ring
