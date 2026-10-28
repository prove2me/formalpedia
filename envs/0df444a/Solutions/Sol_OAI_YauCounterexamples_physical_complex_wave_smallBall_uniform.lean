-- Prove2me | solution 1 for OAI.YauCounterexamples.physical_complex_wave_smallBall_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:22:38.367006+00:00
-- url     : https://prove2.me/submissions/b2437e47-ee55-4cc0-a9d6-ae6651c259c7

import Mathlib
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_GaussianPDFStandardOne
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
namespace YauCounterexamples

theorem gaussianPDF_standard_le_one (m x : ℝ) : gaussianPDF m 1 x ≤ 1 := by
  rw [gaussianPDF, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one]
  have hexp : Real.exp (-(x - m) ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hroot
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x - m) ^ 2 / 2) ≤
        (Real.sqrt (2 * Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 1 := by simpa using hinv

theorem gaussianReal_standard_le_volume (m : ℝ) : gaussianReal m 1 ≤ volume := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  calc
    volume.withDensity (gaussianPDF m 1) ≤ volume.withDensity (fun _ => 1) :=
      withDensity_mono (Filter.Eventually.of_forall (gaussianPDF_standard_le_one m))
    _ = volume := by simp

theorem finite_pi_measure_mono {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ ν : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have hle : (Measure.pi μ).toOuterMeasure ≤ OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro s _
    rw [Measure.coe_toOuterMeasure, Measure.pi_pi]
    exact Finset.prod_le_prod' (fun index _ => h index (s index))
  apply Measure.le_iff.mpr
  intro s hs
  conv_rhs => rw [Measure.pi, toMeasure_apply _ _ hs]
  exact hle s

theorem gaussian_pi_le_volume {ι : Type*} [Fintype ι] (m : ι → ℝ) :
    Measure.pi (fun i => gaussianReal (m i) 1) ≤ (volume : Measure (ι → ℝ)) :=
  finite_pi_measure_mono _ _ (fun i => gaussianReal_standard_le_volume (m i))

theorem gaussian_affine_map_le {ι : Type*} [Fintype ι]
    (m b : ι → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hL : LinearMap.det L ≠ 0) :
    (Measure.pi (fun i => gaussianReal (m i) 1)).map (fun x => L x + b) ≤
      ENNReal.ofReal (abs (LinearMap.det L)⁻¹) • (volume : Measure (ι → ℝ)) := by
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hb : Measurable (fun x : ι → ℝ => x + b) := measurable_id.add measurable_const
  calc
    (Measure.pi (fun i => gaussianReal (m i) 1)).map (fun x => L x + b) ≤
        volume.map (fun x => L x + b) :=
      Measure.map_mono (gaussian_pi_le_volume m) (hLm.add measurable_const)
    _ = ENNReal.ofReal (abs (LinearMap.det L)⁻¹) • volume := by
      rw [show (fun x => L x + b) = (fun x => x + b) ∘ L from rfl,
        ← Measure.map_map hb hLm, Real.map_linearMap_volume_pi_eq_smul_volume_pi hL,
        Measure.map_smul, map_add_right_eq_self]

theorem gaussian_affine_smallBall {ι : Type*} [Fintype ι]
    (m b c : ι → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hL : LinearMap.det L ≠ 0)
    (r : ℝ) (hr : 0 ≤ r) :
    (Measure.pi (fun i => gaussianReal (m i) 1))
      ((fun x => L x + b) ⁻¹' Metric.closedBall c r) ≤
      ENNReal.ofReal (abs (LinearMap.det L)⁻¹) *
        (ENNReal.ofReal (2 * r)) ^ Fintype.card ι := by
  have hm : Measurable (fun x => L x + b) :=
    L.continuous_of_finiteDimensional.measurable.add measurable_const
  rw [← Measure.map_apply hm measurableSet_closedBall]
  calc
    _ ≤ (ENNReal.ofReal (abs (LinearMap.det L)⁻¹) • volume) (Metric.closedBall c r) :=
      gaussian_affine_map_le m b L hL _
    _ = _ := by
      rw [Measure.smul_apply, smul_eq_mul, volume_pi_closedBall c hr]
      simp [Real.volume_closedBall]

theorem gaussian_independent_smallBall {ι : Type*} [Fintype ι]
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (g : Ω → (ι → ℝ)) (hg : Measurable g)
    (m c : ι → ℝ) (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hL : LinearMap.det L ≠ 0)
    (r : ℝ) (hr : 0 ≤ r) :
    (ν.prod (Measure.pi (fun i => gaussianReal (m i) 1)))
      {w | L w.2 + g w.1 ∈ Metric.closedBall c r} ≤
      ENNReal.ofReal (abs (LinearMap.det L)⁻¹) *
        (ENNReal.ofReal (2 * r)) ^ Fintype.card ι := by
  have hmeas : Measurable (fun w : Ω × (ι → ℝ) => L w.2 + g w.1) :=
    (L.continuous_of_finiteDimensional.measurable.comp measurable_snd).add
      (hg.comp measurable_fst)
  change (ν.prod (Measure.pi (fun i => gaussianReal (m i) 1)))
    ((fun w : Ω × (ι → ℝ) => L w.2 + g w.1) ⁻¹' Metric.closedBall c r) ≤ _
  rw [Measure.prod_apply (hmeas measurableSet_closedBall)]
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (abs (LinearMap.det L)⁻¹) *
        (ENNReal.ofReal (2 * r)) ^ Fintype.card ι ∂ν := by
      apply lintegral_mono
      intro w
      exact gaussian_affine_smallBall m (g w) c L hL r hr
    _ = _ := by simp

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_WaveJetMatrix
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology Matrix ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples

theorem contDiff_matrixDet {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContDiff ℝ ∞ (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  change ContDiff ℝ ∞ (fun A : Matrix ι ι ℝ => Matrix.det A)
  simp only [Matrix.det_apply]
  fun_prop

theorem determinant_uniform_error_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C d : ℝ) (hC : 0 ≤ C) (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ A R : Matrix ι ι ℝ, ‖A‖ ≤ M → d * δ ≤ |A.det| →
        ‖R‖ ≤ C * δ ^ 2 → d / 2 * δ ≤ |(A + R).det| := by
  obtain ⟨K, hK⟩ := (contDiff_matrixDet (ι := ι)).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0 : Matrix ι ι ℝ) (M + 1))
    (isCompact_closedBall (0 : Matrix ι ι ℝ) (M + 1))
  refine ⟨min 1 (min (1 / (C + 1)) (d / (2 * ((K : ℝ) + 1) * (C + 1)))), ?_, ?_⟩
  · exact lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  intro δ hδ hδε A R hA hdet hR
  have hδ1 : δ < 1 := hδε.trans_le (min_le_left _ _)
  have hδC : δ < 1 / (C + 1) := hδε.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδd : δ < d / (2 * ((K : ℝ) + 1) * (C + 1)) := hδε.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hCδ : C * δ < 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hδC
    nlinarith
  have hR1 : ‖R‖ < 1 := by
    have hsq : δ ^ 2 ≤ δ := by nlinarith
    have := mul_le_mul_of_nonneg_left hsq hC
    linarith
  have hAs : A ∈ Metric.closedBall 0 (M + 1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (by linarith : ‖A‖ ≤ M + 1)
  have hARs : A + R ∈ Metric.closedBall 0 (M + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le A R).trans (by linarith)
  have hdiff := hK.dist_le_mul (x := A + R) hARs (y := A) hAs
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at hdiff
  have hKδ : (K : ℝ) * C * δ ^ 2 ≤ d / 2 * δ := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * ((K : ℝ) + 1) * (C + 1))).mp hδd
    have hkk : (K : ℝ) * C ≤ ((K : ℝ) + 1) * (C + 1) := by
      nlinarith [K.coe_nonneg]
    have hmm := mul_le_mul_of_nonneg_right hkk hδ.le
    have hp := mul_le_mul_of_nonneg_right hmm hδ.le
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hR K.coe_nonneg
  have htriangle : |A.det| ≤ |(A + R).det - A.det| + |(A + R).det| := by
    simpa only [sub_add_cancel, abs_sub_comm] using
      abs_add_le (A.det - (A + R).det) (A + R).det
  nlinarith

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_ProductMetric_FourColumnSmallBall
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology Matrix ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
open MeasureTheory ProbabilityTheory

theorem column_scaled_det_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (c : ι → ℝ) (d q : ℝ)
    (hq : 0 ≤ q) (hdet : d ≤ |A.det|)
    (hc : ∀ i, q ≤ c i) :
    d * q ^ Fintype.card ι ≤ |(A * Matrix.diagonal c).det| := by
  rw [Matrix.det_mul, Matrix.det_diagonal, abs_mul]
  have hprod : q ^ Fintype.card ι ≤ ∏ i, c i := by
    calc
      _ = ∏ _i : ι, q := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hq) (fun index _ => hc index)
  have hpzero : 0 ≤ ∏ i, c i := Finset.prod_nonneg (fun i _ => hq.trans (hc i))
  rw [abs_of_nonneg hpzero]
  exact mul_le_mul hdet hprod (pow_nonneg hq _) (abs_nonneg _)

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ComplexPolarWeight
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology Matrix Matrix.Norms.Elementwise ENNReal

lemma phaseFrameMatrix_gram (ν b c : PhaseSpace) :
    (phaseFrameMatrix ν b c)ᵀ * phaseFrameMatrix ν b c =
      !![inner ℝ ν ν,inner ℝ ν b,inner ℝ ν c;
         inner ℝ b ν,inner ℝ b b,inner ℝ b c;
         inner ℝ c ν,inner ℝ c b,inner ℝ c c] := by
  simp_rw [PiLp.inner_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseFrameMatrix,Matrix.mul_apply,Fin.sum_univ_succ,mul_comm,pow_two]

lemma phaseFrameMatrix_det_sq (ν b c : PhaseSpace) (hν : ‖ν‖ = 1)
    (hb : inner ℝ ν b = 0) (hc : inner ℝ ν c = 0) :
    (phaseFrameMatrix ν b c).det^2 = ‖b‖^2*‖c‖^2-(inner ℝ b c)^2 := by
  have h := congrArg Matrix.det (phaseFrameMatrix_gram ν b c)
  rw [Matrix.det_mul,Matrix.det_transpose] at h
  conv_rhs at h => rw [Matrix.det_fin_three]
  simpa [real_inner_self_eq_norm_sq,hν,hb,hc,real_inner_comm c b,pow_two] using h

lemma physicalWaveJetMatrix_det (a ν b c : PhaseSpace) (δ : ℝ) :
    (physicalWaveJetMatrix a ν b c δ).det = δ*(phaseFrameMatrix ν b c).det := by
  rw [physicalWaveJetMatrix,Matrix.det_fromBlocks_one₁₁]
  simp [phaseFrameMatrix,Matrix.det_fin_three,Matrix.sub_apply,Matrix.mul_apply]
  ring

lemma phaseFrameMatrix_det_lower (a ν b c : PhaseSpace) (η : ℝ)
    (hν : ‖ν‖ = 1) (hb : inner ℝ ν b = 0) (hc : inner ℝ ν c = 0)
    (hbn : ‖b‖^2 = 1+‖a‖^2) (hcn : ‖c‖^2 = 1+‖a‖^2)
    (hη : 0 < η) (hangle : η ≤ transverseAngleSq b c) :
    Real.sqrt η ≤ |(phaseFrameMatrix ν b c).det| := by
  have hL : 1 ≤ ‖b‖^2*‖c‖^2 := by rw [hbn,hcn]; nlinarith [sq_nonneg ‖a‖]
  have hh : η*(‖b‖^2*‖c‖^2) ≤ ‖b‖^2*‖c‖^2-(inner ℝ b c)^2 :=
    (le_div_iff₀ (zero_lt_one.trans_le hL)).mp hangle
  have hmul : η ≤ η*(‖b‖^2*‖c‖^2) := by nlinarith
  have hsq : η ≤ (phaseFrameMatrix ν b c).det^2 := by
    rw [phaseFrameMatrix_det_sq ν b c hν hb hc]
    exact hmul.trans hh
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hsq

lemma physicalWaveJetMatrix_det_lower (a ν b c : PhaseSpace) (δ η : ℝ)
    (hν : ‖ν‖ = 1) (hb : inner ℝ ν b = 0) (hc : inner ℝ ν c = 0)
    (hbn : ‖b‖^2 = 1+‖a‖^2) (hcn : ‖c‖^2 = 1+‖a‖^2)
    (hη : 0 < η) (hangle : η ≤ transverseAngleSq b c) (hδ : 0 ≤ δ) :
    Real.sqrt η*δ ≤ |(physicalWaveJetMatrix a ν b c δ).det| := by
  rw [physicalWaveJetMatrix_det,abs_mul,abs_of_nonneg hδ]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (phaseFrameMatrix_det_lower a ν b c η hν hb hc hbn hcn hη hangle) hδ

lemma physicalWaveJetMatrix_bound (a ν b c : PhaseSpace) (δ M : ℝ)
    (hM : 1 ≤ M) (ha : ‖a‖ ≤ M) (hν : ‖ν‖ = 1)
    (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ‖physicalWaveJetMatrix a ν b c δ‖ ≤ M+1 := by
  apply (Matrix.norm_le_iff (by linarith : 0 ≤ M+1)).mpr
  intro i j
  rcases i with i|i <;> rcases j with j|j
  · fin_cases i; fin_cases j
    norm_num [physicalWaveJetMatrix]
    linarith
  · fin_cases j <;> simp [physicalWaveJetMatrix] <;> linarith
  · simpa [physicalWaveJetMatrix] using (PiLp.norm_apply_le a i).trans (ha.trans (by linarith))
  · fin_cases j
    · change ‖a i+δ*ν i‖ ≤ M+1
      calc
        _ ≤ ‖a i‖+‖δ*ν i‖ := norm_add_le _ _
        _ = ‖a i‖+δ*‖ν i‖ := by rw [norm_mul,Real.norm_of_nonneg hδ]
        _ ≤ M+δ*1 := add_le_add ((PiLp.norm_apply_le a i).trans ha)
          (mul_le_mul_of_nonneg_left (by simpa [hν] using PiLp.norm_apply_le ν i) hδ)
        _ ≤ M+1 := by linarith
    · simpa [physicalWaveJetMatrix] using (PiLp.norm_apply_le b i).trans (hb.trans (by linarith))
    · simpa [physicalWaveJetMatrix] using (PiLp.norm_apply_le c i).trans (hc.trans (by linarith))


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ENNReal Matrix.Norms.Elementwise


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ComplexGaussianRealValue
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma complex_stdGaussian_eq_map :
    stdGaussian ℂ = (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map
      (fun x => (x 0 : ℂ)+(x 1 : ℂ)*Complex.I) := by
  simpa [Complex.coe_orthonormalBasisOneI,Fin.sum_univ_two,Algebra.smul_def]
    using stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI

lemma complex_gaussian_pair :
    MeasurePreserving (fun x : ℝ × ℝ => (x.1 : ℂ)+(x.2 : ℂ)*Complex.I)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) (stdGaussian ℂ) := by
  have hp := (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 1)).symm
  have hm : MeasurePreserving (fun x : Fin 2 → ℝ => (x 0 : ℂ)+(x 1 : ℂ)*Complex.I)
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) (stdGaussian ℂ) :=
    ⟨by fun_prop,complex_stdGaussian_eq_map.symm⟩
  exact hm.comp hp

lemma gaussian_complex_rotation (e : Circle) :
    MeasurePreserving (fun z : ℂ => (e : ℂ)*z) (stdGaussian ℂ) (stdGaussian ℂ) :=
  ⟨(rotation e).continuous.measurable,stdGaussian_map (rotation e)⟩

lemma gaussian_complex_conj :
    MeasurePreserving (starRingEnd ℂ) (stdGaussian ℂ) (stdGaussian ℂ) :=
  ⟨Complex.continuous_conj.measurable,stdGaussian_map Complex.conjLIE⟩

lemma gaussian_complex_pi_rotation {ι : Type*} [Fintype ι] (e : ι → Circle) :
    MeasurePreserving (fun z : ι → ℂ => fun i => (e i : ℂ)*z i)
      (Measure.pi (fun _ : ι => stdGaussian ℂ)) (Measure.pi (fun _ : ι => stdGaussian ℂ)) :=
  measurePreserving_pi _ _ (fun i => gaussian_complex_rotation (e i))

lemma gaussian_complex_from_real_parts {ι : Type*} [Fintype ι] :
    MeasurePreserving (fun x : (ι ⊕ ι) → ℝ =>
      fun i => (x (.inl i) : ℂ)-(x (.inr i) : ℂ)*Complex.I)
      (Measure.pi (fun _ : ι ⊕ ι => gaussianReal 0 1))
      (Measure.pi (fun _ : ι => stdGaussian ℂ)) := by
  have hsplit := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)
  have hpair := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).symm
  have hc := gaussian_complex_conj.comp complex_gaussian_pair
  have hpi := measurePreserving_pi (fun _ : ι => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ : ι => stdGaussian ℂ) (fun _ => hc)
  convert hpi.comp (hpair.comp hsplit) using 1
  all_goals try with_reducible_and_instances rfl
  ext x i
  simp [Function.comp_def,MeasurableEquiv.sumPiEquivProdPi,
    MeasurableEquiv.arrowProdEquivProdArrow, Complex.conj_ofReal,sub_eq_add_neg]

lemma selectedComplexCoefficients_law :
    MeasurePreserving selectedComplexCoefficients
      ((Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin 1 ⊕ Fin 3 => gaussianReal 0 1)))
      (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)) := by
  have hsplit := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin 2 ⊕ (Fin 1 ⊕ Fin 3) => gaussianReal 0 1)
  have hreorder := measurePreserving_piCongrLeft
    (fun _ : Fin 3 ⊕ Fin 3 => gaussianReal 0 1) selectedCoefficientOrder.symm
  have h := gaussian_complex_from_real_parts.comp (hreorder.comp hsplit)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext v i
  fin_cases i <;> rfl


end


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ComplexRealResponse
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal Topology Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma complexRealResponse_selected (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ)
    (v : (Fin 2 → ℝ) × ((Fin 1 ⊕ Fin 3) → ℝ)) :
    complexRealResponse J (selectedComplexCoefficients v) =
      Matrix.toLin' (selectedComplexJetMatrix J) v.2 +
        (fun i => v.1 0*(J 1 i).re+v.1 1*(J 2 i).im) := by
  ext i
  simp [complexRealResponse,selectedComplexCoefficients,selectedComplexJetMatrix,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_succ,
    Complex.mul_re,Complex.mul_im]
  ring

lemma measurable_complexRealResponse {ι : Type*} (J : Fin 3 → ι → ℂ) :
    Measurable (complexRealResponse J) := by
  unfold complexRealResponse
  fun_prop

theorem complex_three_wave_smallBall {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)) (hn : Measurable noise)
    (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ)
    (d : ℝ) (hd : 0 < d) (hdet : d ≤ |(selectedComplexJetMatrix J).det|)
    (r : ℝ) (hr : 0 ≤ r) :
    (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {v | complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} ≤
      ENNReal.ofReal d⁻¹*(ENNReal.ofReal (2*r))^4 := by
  let μ2 := Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)
  let μ4 := Measure.pi (fun _ : Fin 1 ⊕ Fin 3 => gaussianReal 0 1)
  let extra : Ω × (Fin 2 → ℝ) → ((Fin 1 ⊕ Fin 3) → ℝ) :=
    fun v i => v.2 0*(J 1 i).re+v.2 1*(J 2 i).im+noise v.1 i
  have he : Measurable extra := by unfold extra; fun_prop
  have hne : LinearMap.det (Matrix.toLin' (selectedComplexJetMatrix J)) ≠ 0 := by
    rw [LinearMap.det_toLin']
    exact abs_pos.mp (hd.trans_le hdet)
  have hb := gaussian_independent_smallBall (μ.prod μ2) extra he (fun _ => 0) 0
    (Matrix.toLin' (selectedComplexJetMatrix J)) hne r hr
  norm_num only [Fintype.card_sum,Fintype.card_fin] at hb
  have hpr := ((MeasurePreserving.id μ).prod selectedComplexCoefficients_law).comp
    (measurePreserving_prodAssoc μ μ2 μ4)
  have hs : MeasurableSet {v : Ω × (Fin 3 → ℂ) |
      complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} :=
    ((measurable_complexRealResponse J).comp measurable_snd |>.add
        (hn.comp measurable_fst)) Metric.isClosed_closedBall.measurableSet
  have hp := hpr.measure_preimage hs.nullMeasurableSet
  rw [←hp]
  have hset : (Prod.map id selectedComplexCoefficients ∘ ⇑MeasurableEquiv.prodAssoc) ⁻¹'
      {v | complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} =
      {v : (Ω × (Fin 2 → ℝ)) × ((Fin 1 ⊕ Fin 3) → ℝ) |
        Matrix.toLin' (selectedComplexJetMatrix J) v.2+extra v.1 ∈ Metric.closedBall 0 r} := by
    ext v
    change complexRealResponse J (selectedComplexCoefficients (v.1.2,v.2))+noise v.1.1 ∈ Metric.closedBall 0 r ↔
      Matrix.toLin' (selectedComplexJetMatrix J) v.2+extra v.1 ∈ Metric.closedBall 0 r
    rw [complexRealResponse_selected]
    have hv : (Matrix.toLin' (selectedComplexJetMatrix J) v.2 +
        (fun i => v.1.2 0*(J 1 i).re+v.1.2 1*(J 2 i).im))+noise v.1.1 =
        Matrix.toLin' (selectedComplexJetMatrix J) v.2+extra v.1 := by
      ext i
      simp [extra,add_assoc]
    change (_+_)+noise v.1.1 ∈ Metric.closedBall 0 r ↔ _+_ ∈ Metric.closedBall 0 r
    rw [hv]
  rw [hset]
  apply hb.trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  rw [LinearMap.det_toLin',abs_inv]
  exact inv_anti₀ hd hdet

lemma complexRealResponse_rotation (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ)
    (e : Fin 3 → Circle) (γ : Fin 3 → ℂ) :
    complexRealResponse (fun ℓ i => (e ℓ : ℂ)*J ℓ i) γ =
      complexRealResponse J (fun ℓ => (e ℓ : ℂ)*γ ℓ) := by
  ext i
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 1
  ring

theorem complex_three_wave_rotated_smallBall {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)) (hn : Measurable noise)
    (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ) (e : Fin 3 → Circle)
    (d : ℝ) (hd : 0 < d) (hdet : d ≤ |(selectedComplexJetMatrix J).det|)
    (r : ℝ) (hr : 0 ≤ r) :
    (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {v | complexRealResponse (fun ℓ i => (e ℓ : ℂ)*J ℓ i) v.2+noise v.1 ∈ Metric.closedBall 0 r} ≤
      ENNReal.ofReal d⁻¹*(ENNReal.ofReal (2*r))^4 := by
  have hp := (MeasurePreserving.id μ).prod (gaussian_complex_pi_rotation e)
  have hs : MeasurableSet {v : Ω × (Fin 3 → ℂ) |
      complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} :=
    ((measurable_complexRealResponse J).comp measurable_snd |>.add
        (hn.comp measurable_fst)) Metric.isClosed_closedBall.measurableSet
  have hm := hp.measure_preimage hs.nullMeasurableSet
  have heq : {v : Ω × (Fin 3 → ℂ) |
      complexRealResponse (fun ℓ i => (e ℓ : ℂ)*J ℓ i) v.2+noise v.1 ∈ Metric.closedBall 0 r} =
      (Prod.map id (fun γ ℓ => (e ℓ : ℂ)*γ ℓ)) ⁻¹'
      {v | complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} := by
    ext v
    simp [complexRealResponse_rotation]
  rw [heq,hm]
  exact complex_three_wave_smallBall μ noise hn J d hd hdet r hr

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SelectedComplexJetMatrixScale
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal Topology Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma selectedComplexJetMatrix_scale (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ) (w : Fin 3 → ℝ) :
    selectedComplexJetMatrix (fun ℓ i => (w ℓ : ℂ)*J ℓ i) =
      selectedComplexJetMatrix J * Matrix.diagonal
        (Sum.elim (fun _ : Fin 1 => w 0) (fun k : Fin 3 => ![w 2,w 0,w 1] k)) := by
  ext i j
  rcases j with j|j
  · simp [selectedComplexJetMatrix,Matrix.mul_diagonal,Complex.mul_re,mul_comm]
  · fin_cases j <;> simp [selectedComplexJetMatrix,Matrix.mul_diagonal,Complex.mul_re,Complex.mul_im,mul_comm]

theorem physical_complex_wave_smallBall_uniform_oai (M C η : ℝ) (hM : 1 ≤ M)
    (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ a ν b c : PhaseSpace, ‖a‖ ≤ M → ‖ν‖ = 1 →
        inner ℝ ν b = 0 → inner ℝ ν c = 0 →
        ‖b‖^2 = 1+‖a‖^2 → ‖c‖^2 = 1+‖a‖^2 →
        ‖b‖ ≤ M → ‖c‖ ≤ M → η ≤ transverseAngleSq b c →
      ∀ J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ,
        ‖selectedComplexJetMatrix J-physicalWaveJetMatrix a ν b c δ‖ ≤ C*δ^2 →
      ∀ q : ℝ, 0 < q → ∀ w : Fin 3 → ℝ, (∀ i, q ≤ w i) → ∀ e : Fin 3 → Circle,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ i => (e ℓ : ℂ)*((w ℓ : ℂ)*J ℓ i)) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤
      ENNReal.ofReal (Real.sqrt η/2*δ*q^4)⁻¹*(ENNReal.ofReal (2*r))^4 := by
  have hd : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  obtain ⟨ε,hε,he⟩ := determinant_uniform_error_bound (ι := Fin 1 ⊕ Fin 3) (M+1) C (Real.sqrt η) hC hd
  refine ⟨min ε 1,lt_min hε zero_lt_one,?_⟩
  intro δ hδ hδε a ν b c ha hν hb hc hbn hcn hbM hcM hang J hJ q hq w hw e Ω _ μ _ noise hn r hr
  have hδ1 : δ ≤ 1 := (hδε.trans_le (min_le_right _ _)).le
  have hdet : Real.sqrt η/2*δ ≤ |(selectedComplexJetMatrix J).det| := by
    have h := he δ hδ (hδε.trans_le (min_le_left _ _)) _
      (selectedComplexJetMatrix J-physicalWaveJetMatrix a ν b c δ)
      (physicalWaveJetMatrix_bound a ν b c δ M hM ha hν hbM hcM hδ.le hδ1)
      (physicalWaveJetMatrix_det_lower a ν b c δ η hν hb hc hbn hcn hη hang hδ.le) hJ
    simpa only [add_sub_cancel] using h
  let w' := Sum.elim (fun _ : Fin 1 => w 0) (fun k : Fin 3 => ![w 2,w 0,w 1] k)
  have hw' : ∀ i, q ≤ w' i := by
    rintro (i|i)
    · exact hw 0
    · fin_cases i
      · exact hw 2
      · exact hw 0
      · exact hw 1
  have hbnd := column_scaled_det_lower (selectedComplexJetMatrix J) w'
    (Real.sqrt η/2*δ) q hq.le hdet hw'
  norm_num only [Fintype.card_sum,Fintype.card_fin] at hbnd
  have hsc : Real.sqrt η/2*δ*q^4 ≤
      |(selectedComplexJetMatrix (fun ℓ i => (w ℓ : ℂ)*J ℓ i)).det| := by
    rw [selectedComplexJetMatrix_scale]
    exact hbnd
  exact complex_three_wave_rotated_smallBall μ noise hn _ e _ (by positivity) hsc r hr

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.physical_complex_wave_smallBall_uniform_oai.{u_1} := @OAI.YauCounterexamples.physical_complex_wave_smallBall_uniform_oai.{u_1}
