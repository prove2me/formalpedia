-- Prove2me | solution 1 for TroppMatrixConcentration.ch7_intrinsic_hermitian_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:41:43.77398+00:00
-- url     : https://prove2.me/submissions/d71c6caf-6e5a-4423-aa71-26caf64bc7cc

import Definitions.Def_TroppMatrixConcentration_ch7_intrinsic
import Theorems.Thm_TroppMatrixConcentration_ch6_independent_sum_second_moment
import Theorems.Thm_TroppMatrixConcentration_bernstein_mgf_cgf
import Theorems.Thm_TroppMatrixConcentration_trace_cgf_subadditivity
import Theorems.Thm_TroppMatrixConcentration_ch8_trace_exp_monotone
import Theorems.Thm_TroppMatrixConcentration_ch7_generalized_laplace
import Theorems.Thm_TroppMatrixConcentration_ch7_intrinsic_dimension
import Theorems.Thm_TroppMatrixConcentration_ch3_master_sum_exponential_integrable
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TroppMatrixConcentration
namespace IntrinsicHermBernstein

variable {d : ℕ}

lemma traceFunction_eq_sum (φ : ℝ → ℝ)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    traceFunction φ A = ∑ i, φ (hA.eigenvalues i) := by
  rw [traceFunction, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp

lemma traceExp_eq_sum (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [traceExp, matrixExp,
    ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re]

lemma trace_re_eq_sum (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) :
    (Matrix.trace A).re = ∑ i, hA.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues]
  simp

lemma spec_le (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) {L : ℝ}
    (hb : lambdaMax A ≤ L) : ∀ x ∈ spectrum ℝ A, x ≤ L := by
  intro x hx
  have hfin : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  exact (le_csSup hfin.bddAbove hx).trans hb

lemma matrixExp_smul_eq (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (s : ℝ) :
    matrixExp (s • A) = cfc (fun x => Real.exp (s * x)) A := by
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp
    (hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))),
    ← cfc_comp_const_mul s Real.exp A (by fun_prop) hA.isSelfAdjoint]

lemma trace_re_nonneg {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    0 ≤ (Matrix.trace A).re :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

lemma lambdaMax_zero [NeZero d] : lambdaMax (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  rw [lambdaMax, spectrum.zero_eq, csSup_singleton]

lemma neg_posSemidef (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian)
    (hb : lambdaMax A ≤ 0) : (-A).PosSemidef := by
  have h1 : cfc (fun x : ℝ => x) A ≤ cfc (fun _ : ℝ => (0 : ℝ)) A :=
    cfc_mono (fun x hx => spec_le A hA hb x hx)
  rw [cfc_id' ℝ A hA.isSelfAdjoint, cfc_const_zero] at h1
  simpa using Matrix.le_iff.mp h1

lemma trace_re_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → Matrix (Fin d) (Fin d) ℂ) (hZ : Integrable Z μ) :
    Integrable (fun ω => (Matrix.trace (Z ω)).re) μ :=
  Complex.reCLM.integrable_comp
    ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hZ)

lemma integral_trace_re {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → Matrix (Fin d) (Fin d) ℂ) (hZ : Integrable Z μ) :
    ∫ ω, (Matrix.trace (Z ω)).re ∂μ = (Matrix.trace (∫ ω, Z ω ∂μ)).re := by
  have h1 := Complex.reCLM.integral_comp_comm
    ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integrable_comp hZ)
  have h2 := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.integral_comp_comm hZ
  simp only [Complex.reCLM_apply, LinearMap.coe_toContinuousLinearMap',
    Matrix.traceLinearMap_apply] at h1 h2
  rw [h1, h2]

lemma exp_cubic_le {a : ℝ} (ha : 0 ≤ a) : 1 + a + a ^ 2 / 2 + a ^ 3 / 6 ≤ Real.exp a := by
  have h := Real.sum_le_exp_of_nonneg ha 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- For `a ≥ 1`: `eᵃ ≤ 4 (eᵃ - a - 1)`, i.e. `eᵃ/(eᵃ - a - 1) ≤ 4`. -/
lemma exp_le_four {a : ℝ} (ha : 1 ≤ a) : Real.exp a ≤ 4 * (Real.exp a - a - 1) := by
  have h := exp_cubic_le (by linarith : (0 : ℝ) ≤ a)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) (by nlinarith : (0 : ℝ) ≤ a ^ 2 + 4 * a + 2)]

lemma exp_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NeZero d] (X : Ω → Matrix (Fin d) (Fin d) ℂ) (hMeas : Measurable X)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian) {L θ : ℝ} (hθ : 0 ≤ θ)
    (hBound : ∀ᵐ ω ∂μ, lambdaMax (X ω) ≤ L) :
    Integrable (fun ω => matrixExp (θ • X ω)) μ := by
  have hEcont : Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (θ • A)) := by
    let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ _
    dsimp [matrixExp]
    fun_prop
  refine Integrable.of_bound (hEcont.comp_aestronglyMeasurable hMeas.aestronglyMeasurable)
    (Real.exp (θ * L)) ?_
  filter_upwards [hHerm, hBound] with ω hH hB
  rw [matrixExp_smul_eq _ hH]
  apply norm_cfc_le (Real.exp_pos _).le
  intro x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (spec_le _ hH hB x hx) hθ)

end IntrinsicHermBernstein
end TroppMatrixConcentration

open TroppMatrixConcentration TroppMatrixConcentration.IntrinsicHermBernstein

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ)
    (L : ℝ) (hL : 0 ≤ L) (V : Matrix (Fin d) (Fin d) ℂ) (hV : V ≠ 0)
    (hMeas : ∀ k, Measurable (X k)) (hIndep : iIndepFun X μ)
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hL2 : ∀ k, MemLp (X k) 2 μ)
    (hMean : ∀ k, (∫ ω, X k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (X k ω) ≤ L)
    (hVarianceBound : loewnerLE (∫ ω, (∑ k, X k ω) ^ 2 ∂μ) V) :
    let Y := fun ω => ∑ k, X k ω
    let v := spectralNorm V
    (∫ ω, Y ω ^ 2 ∂μ) = ∑ k, ∫ ω, X k ω ^ 2 ∂μ ∧
    ∀ t : ℝ, Real.sqrt v + L / 3 ≤ t →
      (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
        4 * intrinsicDimension V * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  intro Y v
  -- second moment of the sum
  have hsecond : (∫ ω, Y ω ^ 2 ∂μ) = ∑ k, ∫ ω, X k ω ^ 2 ∂μ := by
    have h := ch6_independent_sum_second_moment μ X id id measurable_id measurable_id
      hMeas hIndep hL2 hL2 hMean
    show (∫ ω, (∑ k, X k ω) ^ 2 ∂μ) = ∑ k, ∫ ω, X k ω ^ 2 ∂μ
    simpa only [id, sq] using h
  refine ⟨hsecond, ?_⟩
  -- basic facts
  have hXint : ∀ k, Integrable (X k) μ := fun k => (hL2 k).integrable one_le_two
  have hYmeas : Measurable Y := Finset.measurable_sum _ (fun k _ => hMeas k)
  have hYHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian := by
    filter_upwards [ae_all_iff.2 hHerm] with ω h
    exact isSelfAdjoint_sum _ (fun k _ => h k)
  have hYint : Integrable Y μ := integrable_finsetSum _ (fun k _ => hXint k)
  have hS : (∫ ω, Y ω ^ 2 ∂μ).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    apply integral_nonneg_of_ae
    filter_upwards [hYHerm] with ω hH
    have : Y ω ^ 2 = Matrix.conjTranspose (Y ω) * Y ω := by rw [hH.eq, sq]
    rw [Pi.zero_apply, this]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).nonneg
  have hVS : (V - ∫ ω, Y ω ^ 2 ∂μ).PosSemidef := hVarianceBound
  have hVpsd : V.PosSemidef := by simpa using hVS.add hS
  have hv : 0 < v := by
    show 0 < ‖V‖
    exact norm_pos_iff.mpr hV
  have hr : 0 ≤ intrinsicDimension V :=
    div_nonneg (trace_re_nonneg hVpsd) (le_of_lt hv)
  intro t ht
  have hsq := Real.sqrt_pos.mpr hv
  have hsqsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
  rcases hL.eq_or_lt with hL0 | hLpos
  · ------------------------------------------------------------ case L = 0
    subst hL0
    have htpos : 0 < t := by linarith
    have hzero : ∀ k, ∀ᵐ ω ∂μ, X k ω = 0 := by
      intro k
      have hneg : ∀ᵐ ω ∂μ, (-X k ω).PosSemidef := by
        filter_upwards [hHerm k, hBound k] with ω hH hB
        exact neg_posSemidef _ hH hB
      have hint : Integrable (fun ω => (Matrix.trace (-X k ω)).re) μ :=
        trace_re_integrable μ (fun ω => -X k ω) (hXint k).neg
      have hnn : 0 ≤ᵐ[μ] fun ω => (Matrix.trace (-X k ω)).re := by
        filter_upwards [hneg] with ω h
        exact trace_re_nonneg h
      have hI : ∫ ω, (Matrix.trace (-X k ω)).re ∂μ = 0 := by
        rw [integral_trace_re μ (fun ω => -X k ω) (hXint k).neg, integral_neg, hMean k]
        simp
      have htr0 := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hI
      filter_upwards [hneg, htr0] with ω h1 h2
      have h3 := Complex.nonneg_iff.mp h1.trace_nonneg
      have htr : Matrix.trace (-X k ω) = 0 :=
        Complex.ext (by simpa using h2) (by simpa using h3.2.symm)
      exact neg_eq_zero.mp (h1.trace_eq_zero_iff.mp htr)
    have hY0 : ∀ᵐ ω ∂μ, Y ω = 0 := by
      filter_upwards [ae_all_iff.2 hzero] with ω h
      show ∑ k, X k ω = 0
      simp [h]
    have hnull : μ {ω | t ≤ lambdaMax (Y ω)} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hY0] with ω h
      simp only [h, lambdaMax_zero, not_le]
      exact htpos
    rw [hnull, ENNReal.toReal_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hr) (Real.exp_pos _).le
  · ------------------------------------------------------------ case L > 0
    have htpos : 0 < t := by linarith [div_pos hLpos (by norm_num : (0 : ℝ) < 3)]
    have hts : Real.sqrt v ≤ t := by linarith [div_pos hLpos (by norm_num : (0 : ℝ) < 3)]
    have hDpos : 0 < v + L * t / 3 := by positivity
    have ht2 : v + L * t / 3 ≤ t ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left ht htpos.le,
        mul_le_mul_of_nonneg_left hts hsq.le]
    obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = t / (v + L * t / 3) := ⟨_, rfl⟩
    have hθ : 0 < θ := by rw [hθdef]; positivity
    have hθL : θ < 3 / L := by
      rw [hθdef, div_lt_div_iff₀ hDpos hLpos]
      linarith
    obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = (θ ^ 2 / 2) / (1 - θ * L / 3) := ⟨_, rfl⟩
    have h1θ : 1 - θ * L / 3 = v / (v + L * t / 3) := by
      rw [hθdef]; field_simp; ring
    have hg0 : 0 ≤ g := by
      rw [hgdef, h1θ]; positivity
    have hgv : g * v = θ * t + -(t ^ 2 / 2) / (v + L * t / 3) := by
      rw [hgdef, h1θ, hθdef]; field_simp; ring
    have ha : 1 ≤ θ * t := by
      rw [hθdef, div_mul_eq_mul_div, ← sq, le_div_iff₀ hDpos]; linarith
    -- the function ψ
    set ψ : ℝ → ℝ := fun x => Real.exp (θ * x) - θ * x - 1 with hψdef
    have hψnn : ∀ x, 0 ≤ ψ x := fun x => by
      simp only [hψdef]; linarith [Real.add_one_le_exp (θ * x)]
    have hψmono : MonotoneOn ψ (Set.Ici 0) := by
      intro x hx y hy hxy
      simp only [hψdef]
      have hx0 : 0 ≤ θ * x := mul_nonneg hθ.le hx
      have h1 := Real.add_one_le_exp (θ * (y - x))
      have h2 : Real.exp (θ * y) = Real.exp (θ * x) * Real.exp (θ * (y - x)) := by
        rw [← Real.exp_add]; ring_nf
      have h3 : 1 ≤ Real.exp (θ * x) := Real.one_le_exp hx0
      have h4 : 0 ≤ θ * (y - x) := mul_nonneg hθ.le (by linarith)
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_left h1 (Real.exp_pos (θ * x)).le]
    have hψt : 0 < ψ t := by
      simp only [hψdef]
      have := Real.add_one_lt_exp (ne_of_gt (mul_pos hθ htpos))
      linarith
    -- integrability
    have hExpk : ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ := fun k =>
      exp_integrable μ (X k) (hMeas k) (hHerm k) hθ.le (hBound k)
    have hYexp : Integrable (fun ω => matrixExp (θ • Y ω)) μ :=
      ch3_master_sum_exponential_integrable μ X θ hMeas hHerm hIndep hExpk
    have hTEint : Integrable (fun ω => traceExp (θ • Y ω)) μ :=
      trace_re_integrable μ _ hYexp
    have hYtrint : Integrable (fun ω => (Matrix.trace (Y ω)).re) μ :=
      trace_re_integrable μ Y hYint
    have hYtr0 : ∫ ω, (Matrix.trace (Y ω)).re ∂μ = 0 := by
      rw [integral_trace_re μ Y hYint]
      have : ∫ ω, Y ω ∂μ = 0 := by
        show ∫ ω, ∑ k, X k ω ∂μ = 0
        rw [integral_finsetSum _ (fun k _ => hXint k)]
        simp [hMean]
      rw [this]; simp
    have hψeq : ∀ᵐ ω ∂μ, traceFunction ψ (Y ω) =
        traceExp (θ • Y ω) - θ * (Matrix.trace (Y ω)).re - d := by
      filter_upwards [hYHerm] with ω hH
      rw [traceFunction_eq_sum ψ _ hH, traceExp_eq_sum _ hH θ, trace_re_eq_sum _ hH]
      simp only [hψdef, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hψint : Integrable (fun ω => traceFunction ψ (Y ω)) μ :=
      ((hTEint.sub (hYtrint.const_mul θ)).sub (integrable_const (d : ℝ))).congr
        (hψeq.mono fun _ h => h.symm)
    have hψI : ∫ ω, traceFunction ψ (Y ω) ∂μ = ∫ ω, traceExp (θ • Y ω) ∂μ - d := by
      have hA : Integrable (fun ω => θ * (Matrix.trace (Y ω)).re) μ := hYtrint.const_mul θ
      have hB : Integrable (fun ω => traceExp (θ • Y ω) - θ * (Matrix.trace (Y ω)).re) μ :=
        hTEint.sub hA
      rw [integral_congr_ae hψeq, integral_sub hB (integrable_const _),
        integral_sub hTEint hA, integral_const_mul, hYtr0]
      simp
    have hLap := ch7_generalized_laplace μ Y ψ hYmeas hYHerm hψnn hψmono hψint t htpos.le hψt
    -- expected trace exponential
    have hE1 : ∫ ω, traceExp (θ • Y ω) ∂μ ≤ traceExp (cumulantSum μ X θ) := by
      calc ∫ ω, traceExp (θ • Y ω) ∂μ = ∫ ω, traceExp (∑ k, θ • X k ω) ∂μ := by
            congr 1; funext ω; show traceExp (θ • ∑ k, X k ω) = _; rw [Finset.smul_sum]
        _ ≤ _ := trace_cgf_subadditivity μ X θ hMeas hHerm hIndep hExpk
    have hcumH : (cumulantSum μ X θ).IsHermitian :=
      isSelfAdjoint_sum _ (fun k _ => by unfold matrixLog; exact IsSelfAdjoint.cfc)
    have hcum : loewnerLE (cumulantSum μ X θ) (g • ∑ k, ∫ ω, X k ω ^ 2 ∂μ) := by
      have hk : ∀ k, loewnerLE (matrixLog (∫ ω, matrixExp (θ • X k ω) ∂μ))
          (g • ∫ ω, X k ω ^ 2 ∂μ) := by
        intro k
        rw [hgdef]
        exact (bernstein_mgf_cgf μ (X k) L θ hLpos hθ hθL (hMeas k) (hHerm k) (hL2 k)
          (hMean k) (hBound k)).2
      unfold loewnerLE cumulantSum
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Matrix.posSemidef_sum _ (fun k _ => hk k)
    rw [← hsecond] at hcum
    have hgS : (g • ∫ ω, Y ω ^ 2 ∂μ).IsHermitian :=
      hS.isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial g))
    have hgV : (g • V).IsHermitian :=
      hVpsd.isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial g))
    have hSV : loewnerLE (g • ∫ ω, Y ω ^ 2 ∂μ) (g • V) := by
      unfold loewnerLE
      rw [← smul_sub]
      exact hVS.smul hg0
    have hE2 : traceExp (cumulantSum μ X θ) ≤ traceExp (g • V) :=
      (ch8_trace_exp_monotone _ _ hcumH hgS hcum).trans
        (ch8_trace_exp_monotone _ _ hgS hgV hSV)
    -- intrinsic dimension
    have hconv : ConvexOn ℝ (Set.Ici 0) (fun x => Real.exp (g * x) - 1) := by
      refine ⟨convex_Ici 0, ?_⟩
      intro x _ y _ a b ha hb hab
      have := convexOn_exp.2 (Set.mem_univ (g * x)) (Set.mem_univ (g * y)) ha hb hab
      simp only [smul_eq_mul] at this ⊢
      have e : g * (a * x + b * y) = a * (g * x) + b * (g * y) := by ring
      rw [e]
      nlinarith [this, hab]
    have hID := ch7_intrinsic_dimension (fun x => Real.exp (g * x) - 1) hconv (by simp) V hVpsd
    have hφeq : traceFunction (fun x => Real.exp (g * x) - 1) V = traceExp (g • V) - d := by
      rw [traceFunction_eq_sum _ _ hVpsd.isHermitian, traceExp_eq_sum _ hVpsd.isHermitian g]
      simp only [Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hnum : ∫ ω, traceFunction ψ (Y ω) ∂μ ≤ intrinsicDimension V * Real.exp (g * v) := by
      rw [hψI]
      have h1 : intrinsicDimension V * (Real.exp (g * spectralNorm V) - 1) ≤
          intrinsicDimension V * Real.exp (g * v) := by
        apply mul_le_mul_of_nonneg_left _ hr
        show Real.exp (g * v) - 1 ≤ Real.exp (g * v)
        linarith
      linarith [hφeq ▸ hID]
    have hfour := exp_le_four ha
    have hE := Real.exp_pos (-(t ^ 2 / 2) / (v + L * t / 3))
    calc (μ {ω | t ≤ lambdaMax (Y ω)}).toReal
        ≤ (∫ ω, traceFunction ψ (Y ω) ∂μ) / ψ t := hLap
      _ ≤ intrinsicDimension V * Real.exp (g * v) / ψ t :=
          div_le_div_of_nonneg_right hnum hψt.le
      _ ≤ 4 * intrinsicDimension V * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
          rw [div_le_iff₀ hψt, hgv, Real.exp_add]
          simp only [hψdef]
          have hrE := mul_nonneg hr hE.le
          nlinarith [mul_le_mul_of_nonneg_left hfour hrE]
