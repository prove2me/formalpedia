-- Prove2me | solution 1 for TroppMatrixConcentration.hermitian_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T01:39:17.492119+00:00
-- url     : https://prove2.me/submissions/d720105b-bec0-4ead-8d37-f927adc18787

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Theorems.Thm_TroppMatrixConcentration_master_bounds
import Theorems.Thm_TroppMatrixConcentration_bernstein_mgf_cgf
import Theorems.Thm_TroppMatrixConcentration_ch6_independent_sum_second_moment
import Theorems.Thm_TroppMatrixConcentration_ch8_trace_exp_monotone
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option autoImplicit false

namespace TroppMatrixConcentration
namespace HermBernstein

/-- Real spectral values of a matrix are bounded in absolute value by the operator norm. -/
lemma abs_le_norm {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ) {x : ℝ}
    (hx : x ∈ spectrum ℝ B) : |x| ≤ ‖B‖ := by
  have h : algebraMap ℝ ℂ x ∈ spectrum ℂ B := (spectrum.algebraMap_mem_iff ℂ).mpr hx
  have := spectrum.norm_le_norm_of_mem h
  simpa using this

lemma traceExp_eq_sum {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  rw [traceExp, matrixExp,
    ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re]

lemma traceExp_le {d : ℕ} [NeZero d] (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian)
    {c : ℝ} (hc : 0 ≤ c) : traceExp (c • B) ≤ d * Real.exp (c * ‖B‖) := by
  rw [traceExp_eq_sum B hB c]
  calc ∑ i, Real.exp (c * hB.eigenvalues i) ≤ ∑ _i : Fin d, Real.exp (c * ‖B‖) := by
        apply Finset.sum_le_sum
        intro i _
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hc
        exact (le_abs_self _).trans (abs_le_norm B (hB.eigenvalues_mem_spectrum_real i))
    _ = d * Real.exp (c * ‖B‖) := by simp

lemma traceExp_pos {d : ℕ} [NeZero d] (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    0 < traceExp H := by
  have h := traceExp_eq_sum H hH 1
  rw [one_smul] at h
  rw [h]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

lemma spec_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) {L : ℝ}
    (hb : lambdaMax A ≤ L) : ∀ x ∈ spectrum ℝ A, x ≤ L := by
  intro x hx
  have hfin : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  exact (le_csSup hfin.bddAbove hx).trans hb

lemma matrixExp_smul_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (s : ℝ) :
    matrixExp (s • A) = cfc (fun x => Real.exp (s * x)) A := by
  rw [matrixExp,
    ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))),
    ← cfc_comp_const_mul s Real.exp A (by fun_prop) hA.isSelfAdjoint]

/-- Scalar optimization for the expectation bound. -/
lemma scalar_expect {x a b L : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ θ : ℝ, 0 < θ → θ < 3 / L →
      x ≤ (a + (θ ^ 2 / 2) / (1 - θ * L / 3) * b) / θ) :
    x ≤ Real.sqrt (2 * b * a) + L * a / 3 := by
  rcases hb.eq_or_lt with rfl | hb'
  · -- variance zero
    simp only [mul_zero, zero_mul, Real.sqrt_zero, zero_add, add_zero] at h ⊢
    by_contra hcon
    push Not at hcon
    have hx : 0 < x := lt_of_le_of_lt (by positivity) hcon
    have h1 : a / x < 3 / L := by
      rw [div_lt_div_iff₀ hx hL]; linarith
    have h2 : a / x < (a / x + 3 / L) / 2 := by linarith
    have h0 : 0 < (a / x + 3 / L) / 2 := lt_of_le_of_lt (div_nonneg ha hx.le) h2
    have h3 := h _ h0 (by linarith)
    rw [div_lt_iff₀ hx] at h2
    rw [le_div_iff₀ h0] at h3
    linarith
  rcases ha.eq_or_lt with rfl | ha'
  · -- `log d = 0`
    simp only [mul_zero, Real.sqrt_zero, zero_div, zero_add] at h ⊢
    by_contra hcon
    push Not at hcon
    set D := b + 2 * x * L / 3 with hDdef
    have hD : 0 < D := by positivity
    have h0 : 0 < x / D := div_pos hcon hD
    have hθD : x / D * D = x := div_mul_cancel₀ x hD.ne'
    have hθL : x / D < 3 / L := by
      rw [div_lt_div_iff₀ hD hL]; nlinarith
    have hq : 0 < 1 - x / D * L / 3 := by
      have : x / D * L < 3 := by
        have := (div_lt_div_iff₀ hD hL).mp hθL
        rw [div_mul_eq_mul_div, div_lt_iff₀ hD]; linarith
      linarith
    have h3 := h _ h0 hθL
    have e : (x / D) ^ 2 / 2 / (1 - x / D * L / 3) * b / (x / D) =
        x / D * b / (2 * (1 - x / D * L / 3)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)] at h3
    set θ := x / D
    rw [hDdef] at hθD
    nlinarith
  · -- generic case
    set r := Real.sqrt (2 * b * a) with hrdef
    have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
    have hr2 : r ^ 2 = 2 * b * a := Real.sq_sqrt (by positivity)
    set s := r / b with hsdef
    have hs : 0 < s := div_pos hr hb'
    set u := 1 + s * L / 3 with hudef
    have hu : 0 < u := by positivity
    have hθ0 : 0 < s / u := div_pos hs hu
    have hθL : s / u < 3 / L := by
      rw [div_lt_div_iff₀ hu hL, hudef]; nlinarith
    have hq : 1 - s / u * L / 3 = 1 / u := by
      field_simp
      rw [hudef]; ring
    have h3 := h (s / u) hθ0 hθL
    rw [hq] at h3
    have e : (a + (s / u) ^ 2 / 2 / (1 / u) * b) / (s / u) =
        a / s + a * L / 3 + s * b / 2 := by
      field_simp
      rw [hudef]; ring
    have e2 : a / s = r / 2 := by
      rw [hsdef]; field_simp; nlinarith [hr2]
    have e3 : s * b / 2 = r / 2 := by
      rw [hsdef]; field_simp
    rw [e, e2, e3] at h3
    linarith

/-- Scalar optimization for the tail bound. -/
lemma scalar_tail {P c v L t : ℝ} (hL : 0 < L) (hv : 0 ≤ v) (ht : 0 < t)
    (h : ∀ θ : ℝ, 0 < θ → θ < 3 / L →
      P ≤ c * Real.exp (-θ * t + (θ ^ 2 / 2) / (1 - θ * L / 3) * v)) :
    P ≤ c * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  rcases hv.eq_or_lt with rfl | hv'
  · have h0 : 0 < 3 / (2 * L) := by positivity
    have h1 : 3 / (2 * L) < 3 / L := by
      rw [div_lt_div_iff₀ (by positivity) hL]; nlinarith
    have h3 := h _ h0 h1
    have e : -(3 / (2 * L)) * t + (3 / (2 * L)) ^ 2 / 2 / (1 - 3 / (2 * L) * L / 3) * 0 =
        -(t ^ 2 / 2) / (0 + L * t / 3) := by
      field_simp
      ring
    rwa [e] at h3
  · set D := v + L * t / 3 with hDdef
    have hD : 0 < D := by positivity
    have h0 : 0 < t / D := div_pos ht hD
    have h1 : t / D < 3 / L := by
      rw [div_lt_div_iff₀ hD hL, hDdef]; nlinarith
    have hq : 1 - t / D * L / 3 = v / D := by
      field_simp
      rw [hDdef]; ring
    have h3 := h _ h0 h1
    rw [hq] at h3
    have e : -(t / D) * t + (t / D) ^ 2 / 2 / (v / D) * v = -(t ^ 2 / 2) / D := by
      field_simp
      ring
    rwa [e] at h3

end HermBernstein
end TroppMatrixConcentration

open TroppMatrixConcentration TroppMatrixConcentration.HermBernstein

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d N : ℕ} [NeZero d]
    (X : Fin N → Ω → Matrix (Fin d) (Fin d) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (X k))
    (hHerm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (hIndep : iIndepFun X μ)
    (hMean : ∀ k, (∫ ω, X k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (X k ω) ≤ L) :
    let Y := fun ω => ∑ k, X k ω
    let v := hermitianSecondMoment μ Y
    v = spectralNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ) ∧
    (∫ ω, lambdaMax (Y ω) ∂μ) ≤
      Real.sqrt (2 * v * Real.log d) + L * Real.log d / 3 ∧
    ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
      bernsteinTail d v L t := by
  intro Y v
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le one_pos hd
  -- the second moment of the sum
  have hsm : (∫ ω, Y ω ^ 2 ∂μ) = ∑ k, ∫ ω, X k ω ^ 2 ∂μ := by
    have h := ch6_independent_sum_second_moment μ X id id measurable_id measurable_id hMeas
      hIndep (fun k => hL2 k) (fun k => hL2 k) hMean

    simp only [Y, sq]
    exact h
  have hv : v = ‖∑ k, ∫ ω, X k ω ^ 2 ∂μ‖ := by
    show spectralNorm (∫ ω, Y ω ^ 2 ∂μ) = _
    rw [hsm]
    rfl
  have hv0 : 0 ≤ v := hv ▸ norm_nonneg _
  have hBpsd : (∑ k, ∫ ω, X k ω ^ 2 ∂μ).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro k _
    apply Matrix.nonneg_iff_posSemidef.mp
    apply integral_nonneg_of_ae
    filter_upwards [hHerm k] with ω hH
    have : X k ω ^ 2 = Matrix.conjTranspose (X k ω) * X k ω := by rw [hH.eq, sq]
    rw [Pi.zero_apply, this]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).nonneg
  have hBH : (∑ k, ∫ ω, X k ω ^ 2 ∂μ).IsHermitian := hBpsd.isHermitian
  have hP1 : ∀ t : ℝ, (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤ d := fun t =>
    (measureReal_le_one (μ := μ)).trans hd
  have htail0 : bernsteinTail d v L 0 = d := by
    unfold bernsteinTail
    split_ifs with h1 h2
    · rfl
    · exact absurd rfl h2
    · simp
  have htailNonneg : ∀ t, 0 ≤ bernsteinTail d v L t := by
    intro t
    unfold bernsteinTail
    split_ifs <;> positivity
  rcases hL.eq_or_lt with hL0 | hLpos
  · -- `L = 0`: every summand is negative semidefinite, hence so is the sum
    subst hL0
    have hY : ∀ᵐ ω ∂μ, lambdaMax (Y ω) ≤ 0 := by
      have h1 : ∀ᵐ ω ∂μ, ∀ k, (X k ω).IsHermitian ∧ lambdaMax (X k ω) ≤ 0 := by
        rw [ae_all_iff]
        intro k
        filter_upwards [hHerm k, hBound k] with ω h1 h2 using ⟨h1, h2⟩
      filter_upwards [h1] with ω hω
      have hle : (∑ k, X k ω) ≤ 0 := by
        apply Finset.sum_nonpos
        intro k _
        have := le_algebraMap_of_spectrum_le (spec_le _ (hω k).1 (hω k).2)
          (hω k).1.isSelfAdjoint
        simpa using this
      have hYH : (∑ k, X k ω).IsHermitian := isSelfAdjoint_sum _ (fun k _ => (hω k).1)
      have hspec : ∀ x ∈ spectrum ℝ (∑ k, X k ω), x ≤ 0 :=
        (le_algebraMap_iff_spectrum_le (r := (0 : ℝ)) hYH.isSelfAdjoint).mp (by simpa using hle)
      exact Real.sSup_nonpos hspec
    refine ⟨hv, ?_, ?_⟩
    · have h1 : (∫ ω, lambdaMax (Y ω) ∂μ) ≤ 0 := integral_nonpos_of_ae hY
      have h2 : 0 ≤ Real.sqrt (2 * v * Real.log d) + 0 * Real.log d / 3 := by
        rw [zero_mul, zero_div, add_zero]; exact Real.sqrt_nonneg _
      linarith
    · intro t ht
      rcases ht.eq_or_lt with h0 | htp
      · subst h0
        rw [htail0]
        exact hP1 0
      · have hnull : μ {ω | t ≤ lambdaMax (Y ω)} = 0 := by
          rw [measure_eq_zero_iff_ae_notMem]
          filter_upwards [hY] with ω hω
          simp only [not_le]
          linarith
        rw [hnull, ENNReal.toReal_zero]
        exact htailNonneg t
  · -- `L > 0`
    set B := ∑ k, ∫ ω, X k ω ^ 2 ∂μ with hBdef
    have hcumH : ∀ θ : ℝ, (cumulantSum μ X θ).IsHermitian := fun θ =>
      isSelfAdjoint_sum _ (fun k _ => by unfold matrixLog; exact IsSelfAdjoint.cfc)
    have hInt : ∀ k, Integrable (X k) μ := fun k => (hL2 k).integrable one_le_two
    have hEcont : ∀ θ : ℝ,
        Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => matrixExp (θ • A)) := by
      intro θ
      let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
        NormedAlgebra.restrictScalars ℚ ℂ _
      dsimp [matrixExp]
      fun_prop
    have hExp : ∀ θ : ℝ, 0 < θ → ∀ k, Integrable (fun ω => matrixExp (θ • X k ω)) μ := by
      intro θ hθ k
      refine Integrable.of_bound
        ((hEcont θ).comp_aestronglyMeasurable (hMeas k).aestronglyMeasurable)
        (Real.exp (θ * L)) ?_
      filter_upwards [hHerm k, hBound k] with ω hH hB
      rw [matrixExp_smul_eq _ hH]
      apply norm_cfc_le (Real.exp_pos _).le
      intro x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (spec_le _ hH hB x hx) hθ.le)
    have hcgf : ∀ θ : ℝ, 0 < θ → θ < 3 / L →
        traceExp (cumulantSum μ X θ) ≤
          d * Real.exp ((θ ^ 2 / 2) / (1 - θ * L / 3) * v) := by
      intro θ hθ hθL
      have hg : 0 ≤ (θ ^ 2 / 2) / (1 - θ * L / 3) := by
        have : θ * L < 3 := (lt_div_iff₀ hLpos).mp hθL
        apply div_nonneg (by positivity)
        linarith
      have hsum : loewnerLE (cumulantSum μ X θ) (((θ ^ 2 / 2) / (1 - θ * L / 3)) • B) := by
        unfold loewnerLE cumulantSum
        rw [hBdef, Finset.smul_sum, ← Finset.sum_sub_distrib]
        exact Matrix.posSemidef_sum _ (fun k _ => (bernstein_mgf_cgf μ (X k) L θ hLpos hθ hθL
          (hMeas k) (hHerm k) (hL2 k) (hMean k) (hBound k)).2)
      calc traceExp (cumulantSum μ X θ)
          ≤ traceExp (((θ ^ 2 / 2) / (1 - θ * L / 3)) • B) :=
            ch8_trace_exp_monotone _ _ (hcumH θ)
              (hBH.smul (isSelfAdjoint_iff.mpr (star_trivial _))) hsum
        _ ≤ d * Real.exp ((θ ^ 2 / 2) / (1 - θ * L / 3) * ‖B‖) := traceExp_le _ hBH hg
        _ = _ := by rw [hv]
    have hE : ∀ θ : ℝ, 0 < θ → θ < 3 / L →
        (∫ ω, lambdaMax (Y ω) ∂μ) ≤
          (Real.log d + (θ ^ 2 / 2) / (1 - θ * L / 3) * v) / θ := by
      intro θ hθ hθL
      have h1 := ((master_bounds μ X θ hMeas hHerm hInt hIndep (hExp θ hθ)).1 hθ).1
      have hpos : 0 < traceExp (cumulantSum μ X θ) := traceExp_pos _ (hcumH θ)
      have hlog : Real.log (traceExp (cumulantSum μ X θ)) ≤
          Real.log d + (θ ^ 2 / 2) / (1 - θ * L / 3) * v := by
        calc _ ≤ Real.log (d * Real.exp ((θ ^ 2 / 2) / (1 - θ * L / 3) * v)) :=
              Real.log_le_log hpos (hcgf θ hθ hθL)
          _ = _ := by rw [Real.log_mul hd0.ne' (Real.exp_pos _).ne', Real.log_exp]
      exact h1.trans (div_le_div_of_nonneg_right hlog hθ.le)
    have hT : ∀ t : ℝ, ∀ θ : ℝ, 0 < θ → θ < 3 / L →
        (μ {ω | t ≤ lambdaMax (Y ω)}).toReal ≤
          d * Real.exp (-θ * t + (θ ^ 2 / 2) / (1 - θ * L / 3) * v) := by
      intro t θ hθ hθL
      have h1 := ((master_bounds μ X θ hMeas hHerm hInt hIndep (hExp θ hθ)).1 hθ).2 t
      calc _ ≤ Real.exp (-θ * t) * traceExp (cumulantSum μ X θ) := h1
        _ ≤ Real.exp (-θ * t) * (d * Real.exp ((θ ^ 2 / 2) / (1 - θ * L / 3) * v)) :=
            mul_le_mul_of_nonneg_left (hcgf θ hθ hθL) (Real.exp_pos _).le
        _ = _ := by rw [Real.exp_add]; ring
    refine ⟨hv, ?_, ?_⟩
    · have := scalar_expect hLpos (Real.log_nonneg hd) hv0 hE
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this
    · intro t ht
      rcases ht.eq_or_lt with h0 | htp
      · subst h0
        rw [htail0]
        exact hP1 0
      · have hD : v + L * t / 3 ≠ 0 := by
          have := mul_pos hLpos htp
          apply ne_of_gt
          linarith
        unfold bernsteinTail
        rw [if_neg hD]
        exact scalar_tail hLpos hv0 htp (hT t)
