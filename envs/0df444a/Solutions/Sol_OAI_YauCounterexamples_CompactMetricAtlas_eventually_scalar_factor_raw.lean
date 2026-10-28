-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:52:43.649623+00:00
-- url     : https://prove2.me/submissions/a4b4f067-7009-4bb3-8215-bc01767493cb

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_eventually_positive_factor
import Theorems.Thm_OAI_YauCounterexamples_CompactMetricAtlas_eventually_scalar_exactification

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFirstCoefficient (g : SmoothMetric E M) (p : M) (j : CoordIndex E)
    {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (metricFirstCoefficient g p j) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  exact ((hd.mul ha).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold ContDiff Matrix.Norms.Elementwise
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]


theorem exists_smooth_metric_coefficients_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).target) :
    ∃ (a : CoordIndex E → CoordIndex E → E → ℝ) (c : CoordIndex E → E → ℝ),
      (∀ i j, ContDiff ℝ ∞ (a i j)) ∧ (∀ i, ContDiff ℝ ∞ (c i)) ∧
      (∀ y ∈ K, (∀ i j, a i j y = (metricCoefficients g p y)⁻¹ i j) ∧
        (∀ i, c i y = metricFirstCoefficient g p i y)) := by
  let φ : E → Matrix (CoordIndex E) (CoordIndex E) ℝ × (CoordIndex E → ℝ) :=
    fun y => ((metricCoefficients g p y)⁻¹, fun i => metricFirstCoefficient g p i y)
  have hφ : ContDiffOn ℝ ∞ φ (chartAt E p).target := by
    apply ContDiffOn.prodMk
    · exact contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j =>
        contDiffOn_metricInverse g p i j))
    · exact contDiffOn_pi.mpr (fun i y hy =>
        (contDiffAt_metricFirstCoefficient g p i hy).contDiffWithinAt)
  obtain ⟨ψ, hψ, he⟩ := smooth_extension_near_compact hK (chartAt E p).open_target hKs hφ
  refine ⟨fun i j y => (ψ y).1 i j, fun i y => (ψ y).2 i,
    fun i j => contDiff_pi.mp (contDiff_pi.mp hψ.fst i) j,
    fun i => contDiff_pi.mp hψ.snd i, ?_⟩
  intro y hy
  have hh := he.self_of_nhdsSet hy
  exact ⟨fun i j => congrFun (congrFun (congrArg Prod.fst hh.symm) i) j,
    fun i => congrFun (congrArg Prod.snd hh.symm) i⟩


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MomentBesselLp
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma fourierL1_moment_norm {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (n : ℕ) (hn : Module.finrank ℝ E < 2 * (s - n))
    (u : FourierSobolevSpace E ℂ s) :
    Integrable (fun x : E => ‖x‖ ^ n * ‖sobolevFourierL1 hs u x‖) ∧
      (∫ x : E, ‖x‖ ^ n * ‖sobolevFourierL1 hs u x‖) ≤ ‖momentBesselLp n hn‖ * ‖u‖ := by
  let v : Lp ℂ 1 (volume : Measure E) := momentBesselLp n hn • u
  have he : (fun x : E => ‖v x‖) =ᵐ[volume]
      (fun x : E => ‖x‖ ^ n * ‖sobolevFourierL1 hs u x‖) := by
    have hw := ((memLp_bessel_weight hs).ofReal :
      MemLp (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2))) 2).coeFn_toLp
    have hm := ((memLp_moment_bessel_weight n hn).ofReal :
      MemLp (fun x : E => Complex.ofReal (‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2))) 2).coeFn_toLp
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (momentBesselLp n hn) u,
      Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (inverseBesselLp hs) u, hw, hm] with x hx hy hw hm
    change ‖(momentBesselLp n hn • u : Lp ℂ 1 volume) x‖ = _
    rw [hx]
    change ‖(momentBesselLp n hn : E → ℂ) x • u x‖ =
      ‖x‖ ^ n * ‖(inverseBesselLp hs • u : Lp ℂ 1 volume) x‖
    rw [hy]
    change ‖((memLp_moment_bessel_weight n hn).ofReal.toLp _ : E → ℂ) x • u x‖ =
      ‖x‖ ^ n * ‖((memLp_bessel_weight hs).ofReal.toLp _ : E → ℂ) x • u x‖
    erw [hm, hw]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-s / 2)),
      abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-s / 2))]
    ring
  refine ⟨(memLp_one_iff_integrable.mp (Lp.memLp v)).norm.congr he, ?_⟩
  calc
    _ = ∫ x : E, ‖v x‖ := integral_congr_ae he.symm
    _ = ‖v‖ := (L1.norm_eq_integral_norm v).symm
    _ ≤ _ := Lp.norm_smul_le (momentBesselLp n hn) u

theorem sobolevRepresentative_jet_bound {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (n : ℕ) (hn : Module.finrank ℝ E < 2 * (s - n))
    (u : FourierSobolevSpace E ℂ s) (x : E) :
    ‖iteratedFDeriv ℝ n (sobolevRepresentative hs u : E → ℂ) x‖ ≤
      (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * ‖momentBesselLp n hn‖ * ‖u‖ := by
  let v := sobolevFourierL1 hs u
  have hm (j : ℕ) (hj : j ≤ n) : Integrable (fun y : E => ‖y‖ ^ j * ‖v y‖) := by
    apply (fourierL1_moment_norm hs j _ u).1
    have : (j : ℝ) ≤ n := by exact_mod_cast hj
    linarith
  have hf : iteratedFDeriv ℝ n (𝓕 (v : E → ℂ)) =
      𝓕 (fun y => VectorFourier.fourierPowSMulRight (innerSL ℝ) (v : E → ℂ) y n) :=
    Real.iteratedFDeriv_fourier (N := (n : ℕ∞))
      (fun j hj => hm j (by exact_mod_cast hj)) (Lp.aestronglyMeasurable v) le_rfl
  have hneg : (sobolevRepresentative hs u : E → ℂ) =
      (𝓕 (v : E → ℂ)) ∘ (LinearIsometryEquiv.neg ℝ (E := E)) := by
    ext y
    rfl
  rw [hneg, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, hf]
  have hi := VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (hm n le_rfl)
    (Lp.aestronglyMeasurable v)
  calc
    _ ≤ ∫ y : E, ‖VectorFourier.fourierPowSMulRight (innerSL ℝ) (v : E → ℂ) y n‖ := by
      rw [Real.fourier_eq]
      apply (norm_integral_le_integral_norm _).trans_eq
      simp only [Circle.norm_smul]
    _ ≤ ∫ y : E, (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * (‖y‖ ^ n * ‖v y‖) := by
      apply integral_mono hi.norm ((hm n le_rfl).const_mul _)
      intro y
      exact (VectorFourier.norm_fourierPowSMulRight_le _ _ y n).trans_eq (by ring)
    _ = (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * ∫ y : E, ‖y‖ ^ n * ‖v y‖ := integral_const_mul _ _
    _ ≤ (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * (‖momentBesselLp n hn‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (fourierL1_moment_norm hs n hn u).2
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
          (innerSL ℝ (E := E)).opNorm_nonneg) n)
    _ = _ := by ring

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma nonempty_patchCoefficients (i : A.t) : Nonempty (A.PatchCoefficients i) := by
  obtain ⟨a, c, ha, hc, he⟩ := exists_smooth_metric_coefficients_on_compact g (A.p i)
    (isCompact_closedBall ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius)
    (A.localInverse i).in_target
  exact ⟨⟨a, c, ha, hc, fun x hx => (he x (A.χcoord_support i hx)).1,
    fun x hx => (he x (A.χcoord_support i hx)).2⟩⟩

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open scoped Manifold BoundedContinuousFunction ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma chart_jet_representative_bound {s : ℝ} (ht : Module.finrank ℝ E < 2 * s)
    (n : ℕ) (hn : Module.finrank ℝ E < 2 * (s - n))
    (u : A.H s) (i : A.t) (y : E) :
    ‖iteratedFDeriv ℝ n (chartLocalize (E := E) (A.p i) (A.η i) (A.representative s u)) y‖ ≤
      (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * ‖momentBesselLp n hn‖ * ‖u‖ := by
  have he : chartLocalize (E := E) (A.p i) (A.η i) (A.representative s u) =
      sobolevRepresentative ht (u.val i) := by
    ext x
    exact (manifoldSobolevRepresentative_localize A.p A.η
      (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η ht u i x).symm
  rw [he]
  apply (sobolevRepresentative_jet_bound ht n hn (u.val i) y).trans
  gcongr
  exact norm_le_pi_norm u.val i

omit [T2Space M] in

theorem exists_chart_jet_constant {s : ℝ} (N : ℕ)
    (hN : Module.finrank ℝ E < 2 * (s - N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : A.H s,
      A.ChartJetBound N (A.representative s u) (C * ‖u‖) := by
  have ht : Module.finrank ℝ E < 2 * s := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hn (j : Fin (N + 1)) : Module.finrank ℝ E < 2 * (s - (j : ℕ)) := by
    have hj : (j : ℕ) ≤ N := by omega
    have hj' : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
    linarith
  let D (j : Fin (N + 1)) : ℝ :=
    (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ (j : ℕ) * ‖momentBesselLp (j : ℕ) (hn j)‖
  have hD (j : Fin (N + 1)) : 0 ≤ D j := by
    apply mul_nonneg _ (norm_nonneg _)
    exact pow_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
      (innerSL ℝ (E := E)).opNorm_nonneg) _
  refine ⟨1 + ∑ j, D j, by positivity, ?_⟩
  intro u i j hj y
  let a : Fin (N + 1) := ⟨j, by omega⟩
  have hb := A.chart_jet_representative_bound ht j (hn a) u i y
  have hDC : D a ≤ 1 + ∑ j, D j := by
    have := Finset.single_le_sum (fun i _ => hD i) (Finset.mem_univ a)
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_right hDC (norm_nonneg _))

end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set MeasureTheory
open scoped LineDeriv SchwartzMap ContDiff Manifold ENNReal
section CompactL2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_L2_compact_bound (f : 𝓢(E, ℂ)) (K : Set E) (hK : IsCompact K)
    (hsupp : tsupport f ⊆ K) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    ‖f.toLp 2 volume‖ ≤ C * (volume K).toReal ^ (1 / 2 : ℝ) := by
  have he : eLpNorm f 2 volume ≤
      ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) := by
    calc
      eLpNorm f 2 volume ≤ eLpNorm (K.indicator (fun _ : E => (C : ℂ))) 2 volume := by
        apply eLpNorm_mono
        intro x
        by_cases hx : x ∈ K
        · simpa only [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hC] using hb x
        · have hz : f x = 0 := by
            by_contra hn
            exact hx (hsupp (subset_tsupport _ hn))
          simp only [Set.indicator_of_notMem hx, hz, norm_zero, le_refl]
      _ = ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) := by
        rw [eLpNorm_indicator_const₀ hK.measurableSet.nullMeasurableSet (by norm_num) (by norm_num)]
        simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hC, ENNReal.toReal_ofNat]
  rw [SchwartzMap.norm_toLp]
  have hfinite : ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hK.measure_lt_top.ne)
  have ht := ENNReal.toReal_mono hfinite he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_rpow] using ht

lemma schwartz_word_bound_of_jets (f : 𝓢(E, ℂ)) (K : Set E) (hK : IsCompact K)
    (hsupp : tsupport f ⊆ K) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j, j ≤ n → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    SchwartzWordBound n f (C * (volume K).toReal ^ (1 / 2 : ℝ)) := by
  intro j hj w
  apply schwartz_L2_compact_bound _ K hK
    ((SchwartzMap.tsupport_iteratedLineDerivOp_subset _ f).trans hsupp) C hC
  intro x
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  calc
    ‖(iteratedFDeriv ℝ j f x) (fun a => stdOrthonormalBasis ℝ E (w a))‖ ≤
        ‖iteratedFDeriv ℝ j f x‖ * ∏ a, ‖stdOrthonormalBasis ℝ E (w a)‖ :=
      (iteratedFDeriv ℝ j f x).le_opNorm _
    _ = ‖iteratedFDeriv ℝ j f x‖ := by simp
    _ ≤ C := hb j hj x
end CompactL2
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem exists_jet_sobolev_constant (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (f : ManifoldSmoothFunctions E M) (C : ℝ), 0 ≤ C →
      A.ChartJetBound (2 * n) f C → ‖A.ofSmooth (2 * (n : ℝ)) f‖ ≤ D * C := by
  classical
  let K (i : A.t) := (chartAt E (A.p i)) '' tsupport (A.η i)
  have hK (i : A.t) : IsCompact (K i) :=
    isCompact_chartSupport (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _) (A.chart_η i)
  let L : ℝ := (1 + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * Module.finrank ℝ E) ^ n
  let V (i : A.t) : ℝ := (volume (K i)).toReal ^ (1 / 2 : ℝ)
  have hL : 0 ≤ L := by positivity
  have hV (i : A.t) : 0 ≤ V i := Real.rpow_nonneg (ENNReal.toReal_nonneg) _
  refine ⟨1 + L * ∑ i, V i, by positivity, ?_⟩
  intro f C hC hf
  change ‖(A.ofSmooth (2 * (n : ℝ)) f).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  let v := chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
    (A.chart_η i) (A.smooth_η i) f
  change ‖schwartzToSobolev (2 * (n : ℝ)) v‖ ≤ _
  have hb : SchwartzWordBound (2 * n) v (C * V i) := by
    refine schwartz_word_bound_of_jets v (K i) (hK i) ?_ (2 * n) C hC ?_
    · exact closure_minimal (support_chartLocalize (E := E) (A.p i) (A.η i) f) (hK i).isClosed
    · intro j hj x
      exact hf i j hj x
  have hv := sobolev_even_le_word_bound n v (C * V i) hb
  have hvi : V i ≤ ∑ i, V i := Finset.single_le_sum (fun j _ => hV j) (Finset.mem_univ i)
  calc
    ‖schwartzToSobolev (2 * (n : ℝ)) v‖ ≤ L * (C * V i) := hv
    _ = (L * V i) * C := by ring
    _ ≤ (1 + L * ∑ i, V i) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact (mul_le_mul_of_nonneg_left hvi hL).trans (by linarith)

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_CompactMetricInverseJets
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_raw_jet_bound {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {f : E → F} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ h, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact (((hf.contDiffAt (hO.mem_nhds (hKO hx))).continuousAt_iteratedFDeriv
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))))).continuousWithinAt
  choose B hB using hb
  let C := 1+∑ j ∈ Finset.range (h+1), max 0 (B j)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro j hj x hx
  calc
    _ ≤ B j := hB j x hx
    _ ≤ max 0 (B j) := le_max_right _ _
    _ ≤ ∑ j ∈ Finset.range (h+1), max 0 (B j) :=
      Finset.single_le_sum (fun k _ => le_max_left _ _) (Finset.mem_range.mpr (by omega))
    _ ≤ C := by dsimp [C]; linarith


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartJetBoundGlobalValue
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Function
open scoped Topology ContDiff Manifold
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiffOn_chartTransition_for_jets (p q : M) :
    ContDiffOn ℝ ∞ ((chartAt E p).symm.trans (chartAt E q))
      ((chartAt E p).symm.trans (chartAt E q)).source := by
  intro y hy
  have hy' : y ∈ (chartAt E p).target ∧ (chartAt E p).symm y ∈ (chartAt E q).source := hy
  exact (contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hy'.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy'.1))).contDiffWithinAt

theorem compact_chart_jet_transfer (p q : M) {L : Set M} (hL : IsCompact L)
    (hLp : L ⊆ (chartAt E p).source) {K : Set E} (hK : IsCompact K)
    (hKq : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : M → F) (f : E → F), ContDiff ℝ ∞ f →
      tsupport U ⊆ L → (∀ z ∈ (chartAt E p).target, U ((chartAt E p).symm z)=f z) →
      ∀ y ∈ K, ∀ j ≤ m, ∀ B : ℝ, 0 ≤ B →
        (∀ i ≤ j, ‖iteratedFDeriv ℝ i f (chartAt E p ((chartAt E q).symm y))‖ ≤ B) →
        ‖iteratedFDeriv ℝ j (U ∘ (chartAt E q).symm) y‖ ≤ C*B := by
  let c := chartAt E p
  let d := chartAt E q
  let T := (d.symm '' K) ∩ L
  have hT : IsCompact T := (hK.image_of_continuousOn (d.continuousOn_symm.mono hKq)).inter_right hL.isClosed
  have hTd : T ⊆ d.source := by
    rintro x ⟨⟨y,hy,rfl⟩,_⟩
    exact d.map_target (hKq hy)
  let S := d '' T
  have hS : IsCompact S := hT.image_of_continuousOn (d.continuousOn.mono hTd)
  let e := d.symm.trans c
  have hSe : S ⊆ e.source := by
    rintro y ⟨x,hx,rfl⟩
    refine ⟨d.map_source (hTd hx),?_⟩
    change d.symm (d x) ∈ c.source
    rw [d.left_inv (hTd hx)]
    exact hLp hx.2
  obtain ⟨ψ,hψ,heψ⟩ := smooth_extension_near_compact hS e.open_source hSe
    (contDiffOn_chartTransition_for_jets q p)
  obtain ⟨D,hD,hDj⟩ := compact_raw_jet_bound isOpen_univ hK (subset_univ _)
    hψ.contDiffOn m
  let C : ℝ := (m.factorial : ℝ)*D^m+1
  have hCp : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hCp,?_⟩
  intro U f hf hUs hUf y hy j hj B hB hfj
  by_cases hx : d.symm y ∈ L
  · have hyS : y ∈ S := ⟨d.symm y,⟨⟨y,hy,rfl⟩,hx⟩,d.right_inv (hKq hy)⟩
    have hey := hSe hyS
    have heψy : (e : E → E) =ᶠ[𝓝 y] ψ := heψ.filter_mono (nhds_le_nhdsSet hyS)
    have heq : U ∘ d.symm =ᶠ[𝓝 y] f ∘ ψ := by
      filter_upwards [e.open_source.mem_nhds hey,heψy] with z hz hzz
      have hcz : d.symm z ∈ c.source := hz.2
      change U (d.symm z)=f (ψ z)
      rw [←hzz]
      change U (d.symm z)=f (c (d.symm z))
      rw [←hUf _ (c.map_source hcz),c.left_inv hcz]
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
    have hb : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f (ψ y)‖ ≤ B := by
      intro i hi
      rw [←heψy.eq_of_nhds]
      exact hfj i hi
    have hd : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i ψ y‖ ≤ D^i := by
      intro i hi hij
      exact (hDj i (hij.trans hj) y hy).trans (by simpa using pow_le_pow_right₀ hD hi)
    have hbound := norm_iteratedFDeriv_comp_le hf hψ
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))) y hb hd
    apply hbound.trans
    have hfact : (j.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hj
    have hp := pow_le_pow_right₀ hD hj
    have hmul := mul_le_mul hfact hp (pow_nonneg (zero_le_one.trans hD) _) (Nat.cast_nonneg _)
    calc
      _ = ((j.factorial : ℝ)*D^j)*B := by ring
      _ ≤ ((m.factorial : ℝ)*D^m)*B := mul_le_mul_of_nonneg_right hmul hB
      _ ≤ C*B := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hB
  · have hn : d.symm y ∉ tsupport U := fun h => hx (hUs h)
    have he : U ∘ d.symm =ᶠ[𝓝 y] (fun _ => (0:F)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto (d.continuousAt_symm (hKq hy)).tendsto
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    simpa using mul_nonneg hCp.le hB


end

open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

omit [T2Space M] [CompactSpace M] in
lemma chartJetBound_global_value {m : ℕ} {u : M → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hj : A.ChartJetBound m u B) (x : M) :
    ‖u x‖ ≤ (Fintype.card A.t:ℝ)*B := by
  classical
  have hb (i : A.t) : ‖A.η i x*u x‖ ≤ B := by
    by_cases hx : x ∈ tsupport (A.η i)
    · have hxs := A.chart_η i hx
      have h := hj i 0 (Nat.zero_le _) (chartAt E (A.p i) x)
      simpa only [norm_iteratedFDeriv_zero,chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hxs),
        (chartAt E (A.p i)).left_inv hxs] using h
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,norm_zero]
      exact hB
  calc
    ‖u x‖ = ‖∑ i : A.t, A.η i x*u x‖ := by rw [←Finset.sum_mul,A.sum_η,one_mul]
    _ ≤ ∑ i : A.t, ‖A.η i x*u x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : A.t, B := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp

theorem chartJetBound_controls_compact_raw (q : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℂ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℂ) ∞ u →
      ∀ B : ℝ, 0 ≤ B → A.ChartJetBound m u B →
      ∀ y ∈ K, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E q).symm) y‖ ≤ C*B := by
  classical
  choose Cs hCs htrans using fun i : A.t => compact_chart_jet_transfer (F := ℂ) (A.p i) q
    (HasCompactSupport.of_compactSpace (A.η i)) (A.chart_η i) hK hKt m
  let C : ℝ := 1+∑ i : A.t, Cs i
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ i : A.t, Cs i := Finset.sum_nonneg (fun i _ => (hCs i).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  refine ⟨C,hC,?_⟩
  intro u hu B hB hjet y hy j hj
  let U : A.t → M → ℂ := fun i x => A.η i x*u x
  have hU (i : A.t) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℂ) ∞ (U i) := contMDiff_complex_mul (A.smooth_η i) hu
  have hsum : u ∘ (chartAt E q).symm=fun z => ∑ i : A.t, U i ((chartAt E q).symm z) := by
    funext z
    simp only [U,←Finset.sum_mul,A.sum_η,one_mul,Function.comp_apply]
  have hdiff (i : A.t) : ContDiffAt ℝ j (U i ∘ (chartAt E q).symm) y :=
    (contMDiffAt_iff_contDiffAt.mp ((hU i).contMDiffAt.comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) (hKt hy)))).of_le
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
  have hbound (i : A.t) :
      ‖iteratedFDeriv ℝ j (U i ∘ (chartAt E q).symm) y‖ ≤ Cs i*B := by
    apply htrans i (U i) (chartLocalize (E := E) (A.p i) (A.η i) u)
      (contDiff_chartLocalize _ _ _ (HasCompactSupport.of_compactSpace _) (A.chart_η i) (A.smooth_η i) hu)
      tsupport_mul_subset_left
      (fun z hz => (chartLocalize_eq _ _ _ hz).symm) y hy j hj B hB
    intro l hl
    exact hjet i l (hl.trans hj) _
  rw [hsum]
  have hej := iteratedFDeriv_fun_sum_apply (u := Finset.univ) (fun i _ => hdiff i)
  simp only [Function.comp_apply] at hej
  rw [hej]
  calc
    _ ≤ ∑ i : A.t, ‖iteratedFDeriv ℝ j (U i ∘ (chartAt E q).symm) y‖ := norm_sum_le _ _
    _ ≤ ∑ i : A.t, Cs i*B := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (∑ i : A.t, Cs i)*B := (Finset.sum_mul ..).symm
    _ ≤ C*B := mul_le_mul_of_nonneg_right (by change (∑ i : A.t, Cs i) ≤ 1+∑ i : A.t, Cs i; linarith) hB

theorem chartJetBound_controls_real_compact_raw (q : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u →
      ∀ B : ℝ, 0 ≤ B → A.ChartJetBound m (fun x => (u x:ℂ)) B →
      ∀ y ∈ K, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E q).symm) y‖ ≤ C*B := by
  obtain ⟨C,hC,hj⟩ := A.chartJetBound_controls_compact_raw q hK hKt m
  refine ⟨C,hC,?_⟩
  intro u hu B hB hjet y hy j hjm
  have hu' : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℂ) ∞ (fun x => (u x:ℂ)) :=
    Complex.ofRealCLM.contMDiff.comp hu
  have hh := hj _ hu' B hB hjet y hy j hjm
  have hd : ContDiffAt ℝ ∞ (u ∘ (chartAt E q).symm) y :=
    contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) (hKt hy)))
  change ‖iteratedFDeriv ℝ j (Complex.ofRealLI ∘ (u ∘ (chartAt E q).symm)) y‖ ≤ C*B at hh
  rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hd
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))] at hh
  exact hh

theorem chartJetBound_controls_finite_real_raw (tests : List (CoordinateTest E M)) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ), ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u →
      ∀ B : ℝ, 0 ≤ B → A.ChartJetBound m (fun x => (u x:ℂ)) B →
      ∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (u ∘ (chartAt E t.center).symm) y‖ ≤ C*B := by
  classical
  choose Cs hCs hJ using fun t : CoordinateTest E M =>
    A.chartJetBound_controls_real_compact_raw t.center t.isCompact t.inTarget m
  let C := 1+∑ t ∈ tests.toFinset, Cs t
  have hC : 0 < C := by
    have hh : 0 ≤ ∑ t ∈ tests.toFinset, Cs t := Finset.sum_nonneg (fun t _ => (hCs t).le)
    dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro u hu B hB hjet t ht y hy j hj
  apply (hJ t u hu B hB hjet y hy j hj).trans
  apply mul_le_mul_of_nonneg_right _ hB
  have hh := Finset.single_le_sum (fun t (_ : t ∈ tests.toFinset) => (hCs t).le)
    (List.mem_toFinset.mpr ht)
  dsimp [C]; linarith
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ProductFrequencyTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Filter
open scoped Topology

lemma sphereFrequency_atTop : Tendsto sphereFrequency atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
lemma inverseFrequency_zero : Tendsto inverseFrequency atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma inverseFrequency_pow_zero (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun n => inverseFrequency n ^ m) atTop (𝓝 0) := by
  simpa only [zero_pow hm] using inverseFrequency_zero.pow m
lemma sphereFrequency_mul_pow (n m : ℕ) (hn : n ≠ 0) :
    sphereFrequency n * inverseFrequency n ^ (m + 2) =
      inverseFrequency n ^ m + 2 * inverseFrequency n ^ (m + 1) := by
  have hx : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [sphereFrequency, inverseFrequency, pow_add, pow_one, inv_pow]
  field_simp
lemma sphereFrequency_mul_pow_zero (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun n => sphereFrequency n * inverseFrequency n ^ (m + 2))
      atTop (𝓝 0) := by
  have he : (fun n => inverseFrequency n ^ m + 2 * inverseFrequency n ^ (m + 1)) =ᶠ[atTop]
      (fun n => sphereFrequency n * inverseFrequency n ^ (m + 2)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (sphereFrequency_mul_pow n m (by omega)).symm
  apply Tendsto.congr' he
  convert (inverseFrequency_pow_zero m hm).add
    ((inverseFrequency_pow_zero (m + 1) (by omega)).const_mul 2) using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma sphereFrequency_ratio (n P : ℕ) (D : ℝ) (hn : n ≠ 0) :
    sphereFrequency n * (D * inverseFrequency n ^ (P + 8)) /
      inverseFrequency n ^ (P + 4) = D * (inverseFrequency n ^ 2 + 2 * inverseFrequency n ^ 3) := by
  have hx : inverseFrequency n ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hn)
  have hp : P + 8 = (P + 4) + 4 := by omega
  rw [hp, pow_add]
  have he : sphereFrequency n * (D * (inverseFrequency n ^ (P + 4) * inverseFrequency n ^ 4)) /
      inverseFrequency n ^ (P + 4) = D * (sphereFrequency n * inverseFrequency n ^ 4) := by
    field_simp
  rw [he, sphereFrequency_mul_pow n 2 hn]

theorem positive_factor_rates (P : ℕ) (D : ℝ) (hD : 0 < D) :
    Tendsto (fun n => D * inverseFrequency n ^ (P + 8)) atTop (𝓝 0) ∧
    Tendsto (fun n => inverseFrequency n ^ (P + 4)) atTop (𝓝 0) ∧
    Tendsto (fun n => sphereFrequency n * (D * inverseFrequency n ^ (P + 8))) atTop (𝓝 0) ∧
    Tendsto (fun n => sphereFrequency n * inverseFrequency n ^ (P + 4)) atTop (𝓝 0) ∧
    Tendsto (fun n => sphereFrequency n * (D * inverseFrequency n ^ (P + 8)) /
      inverseFrequency n ^ (P + 4)) atTop (𝓝 0) ∧
    ∀ᶠ n in atTop, 0 ≤ D * inverseFrequency n ^ (P + 8) ∧
      0 < inverseFrequency n ^ (P + 4) := by
  have hε : Tendsto (fun n => D * inverseFrequency n ^ (P + 8)) atTop (𝓝 0) := by
    simpa using (inverseFrequency_pow_zero (P + 8) (by omega)).const_mul D
  have hδ := inverseFrequency_pow_zero (P + 4) (by omega)
  have hΛε : Tendsto (fun n => sphereFrequency n * (D * inverseFrequency n ^ (P + 8)))
      atTop (𝓝 0) := by
    convert (sphereFrequency_mul_pow_zero (P + 6) (by omega)).const_mul D using 1
    · ext n; ring
    · simp
  have hΛδ : Tendsto (fun n => sphereFrequency n * inverseFrequency n ^ (P + 4))
      atTop (𝓝 0) := by
    convert sphereFrequency_mul_pow_zero (P + 2) (by omega) using 1
    all_goals try with_reducible_and_instances rfl
  have hratio : Tendsto (fun n => sphereFrequency n * (D * inverseFrequency n ^ (P + 8)) /
      inverseFrequency n ^ (P + 4)) atTop (𝓝 0) := by
    have he := ((inverseFrequency_pow_zero 2 (by omega)).add
      ((inverseFrequency_pow_zero 3 (by omega)).const_mul 2)).const_mul D
    have he' : Tendsto (fun n => D * (inverseFrequency n ^ 2 + 2 * inverseFrequency n ^ 3))
        atTop (𝓝 0) := by simpa using he
    apply he'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (sphereFrequency_ratio n P D (by omega)).symm
  refine ⟨hε, hδ, hΛε, hΛδ, hratio, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : 0 < inverseFrequency n := inv_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  exact ⟨mul_nonneg hD.le (pow_nonneg hp.le _), pow_pos hp _⟩

lemma eventual_output_rate (P : ℕ) (C : ℝ) :
    ∀ᶠ n in atTop, C * inverseFrequency n ^ (P + 4) ≤ inverseFrequency n ^ P := by
  have ht : Tendsto (fun n => C * inverseFrequency n ^ 4) atTop (𝓝 0) := by
    simpa using (inverseFrequency_pow_zero 4 (by omega)).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  calc
    C * inverseFrequency n ^ (P + 4) = (C * inverseFrequency n ^ 4) * inverseFrequency n ^ P := by rw [pow_add]; ring
    _ ≤ 1 * inverseFrequency n ^ P := mul_le_mul_of_nonneg_right hn.le (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) _)
    _ = inverseFrequency n ^ P := one_mul _

end


open Set Filter Function Manifold
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_Mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
namespace YauCounterexamples
open Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] [CompactSpace M] in
lemma ChartJetBound.mono {N : ℕ} {f : M → ℂ} {C D : ℝ}
    (h : A.ChartJetBound N f C) (hCD : C ≤ D) : A.ChartJetBound N f D :=
  fun i j hj y => (h i j hj y).trans hCD

theorem eventually_positive_factor_of_jets
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (N P : ℕ) (hN : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ) - N))
    (b s : ℕ → M → ℝ)
    (hb : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (b n))
    (hsmooth : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (s n))
    (hdata : ∀ᶠ n in atTop,
      A.ChartJetBound (2 * (k + 1)) (fun x => ((b n x - 1 : ℝ) : ℂ))
        (inverseFrequency n ^ (P + 8)) ∧
      A.ChartJetBound (2 * (k + 1)) (fun x => ((s n x - 1 : ℝ) : ℂ))
        (inverseFrequency n ^ (P + 8))) :
    ∀ᶠ n in atTop, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, 0 < u x) ∧
      (∀ x, weightedLaplacian g (b n) u x =
        sphereFrequency n * b n x ^ 3 * u x ^ 5 - sphereFrequency n * s n x * u x) ∧
      A.ChartJetBound N (fun x => ((u x - 1 : ℝ) : ℂ)) (inverseFrequency n ^ P) := by
  have ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  obtain ⟨D, hD, hDbound⟩ := A.exists_jet_sobolev_constant (k + 1)
  obtain ⟨C, hC, hCbound⟩ := A.exists_chart_jet_constant N hN
  obtain ⟨he, hδ, hΛe, hΛδ, hratio, hpos⟩ := positive_factor_rates P D hD
  have hnorms : ∀ᶠ n in atTop,
      ‖A.realOfSmooth _ ht (fun x => b n x - 1) ((hb n).sub contMDiff_const)‖ ≤
        D * inverseFrequency n ^ (P + 8) ∧
      ‖A.realOfSmooth _ ht (fun x => s n x - 1) ((hsmooth n).sub contMDiff_const)‖ ≤
        D * inverseFrequency n ^ (P + 8) := by
    filter_upwards [hdata] with n hn
    have hpow : 0 ≤ inverseFrequency n ^ (P + 8) :=
      pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) _
    constructor
    · exact hDbound ⟨_, Complex.ofRealCLM.contMDiff.comp ((hb n).sub contMDiff_const)⟩ _ hpow hn.1
    · exact hDbound ⟨_, Complex.ofRealCLM.contMDiff.comp ((hsmooth n).sub contMDiff_const)⟩ _ hpow hn.2
  have hex := A.eventually_positive_factor hd B ht b s hb hsmooth sphereFrequency
    (fun n => D * inverseFrequency n ^ (P + 8)) (fun n => inverseFrequency n ^ (P + 4))
    sphereFrequency_atTop he hδ hΛe hΛδ hratio hpos hnorms
  filter_upwards [hex, eventual_output_rate P C] with n hn hr
  obtain ⟨u, hu, hup, hueq, h, hnorm, hv⟩ := hn
  refine ⟨u, hu, hup, hueq, ?_⟩
  have heq : A.representative (2 * ((k + 1 : ℕ) : ℝ)) h.val =
      fun x => ((u x - 1 : ℝ) : ℂ) := by
    ext x
    rw [← A.ofReal_realValue, hv]
  have hout := (hCbound h.val).mono A
    ((mul_le_mul_of_nonneg_left hnorm hC.le).trans hr)
  simpa only [heq] using hout
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_EventuallyPositiveFactorEventualJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
namespace YauCounterexamples
open Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

theorem eventually_positive_factor_of_eventual_jets
    (hd : Module.finrank ℝ E = 3) (B : ∀ i, A.PatchCoefficients i)
    (N P : ℕ) (hN : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)-N))
    (b s : ℕ → M → ℝ)
    (hsmooth : ∀ᶠ n in atTop,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n))
    (hdata : ∀ᶠ n in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8))) :
    ∀ᶠ n in atTop, ∃ v : M → ℝ,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
      (∀ x, weightedLaplacian g (b n) v x =
        sphereFrequency n*b n x^3*v x^5-sphereFrequency n*s n x*v x) ∧
      A.ChartJetBound N (fun x => ((v x-1:ℝ):ℂ)) (inverseFrequency n^P) := by
  classical
  let Good (n : ℕ) := ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n)
  let b' (n : ℕ) : M → ℝ := if Good n then b n else fun _ => 1
  let s' (n : ℕ) : M → ℝ := if Good n then s n else fun _ => 1
  have hb' (n : ℕ) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b' n) := by
    by_cases hn : Good n
    · simpa [b', hn] using hn.1
    · simp only [b', ite_eq_right hn]
      exact contMDiff_const
  have hs' (n : ℕ) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s' n) := by
    by_cases hn : Good n
    · simpa [s', hn] using hn.2
    · simp only [s', ite_eq_right hn]
      exact contMDiff_const
  have hdata' : ∀ᶠ n in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b' n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s' n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) := by
    filter_upwards [hsmooth,hdata] with n hn hj
    change Good n at hn
    simpa only [b',s',ite_eq_left hn] using hj
  have h := A.eventually_positive_factor_of_jets hd B N P hN b' s' hb' hs' hdata'
  filter_upwards [hsmooth,h] with n hn hv
  change Good n at hn
  simpa only [b',s',ite_eq_left hn] using hv
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ExistsSphericalScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

theorem eventually_scalar_factor_raw_oai
    (hd : Module.finrank ℝ E=3) (tests : List (CoordinateTest E M))
    (N P B D : ℕ) (hNP : N ≤ 2*(k+1))
    (hN : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)-N))
    (hD : (P+8)+((2*B+21)*(2*(k+1)+2)+10)+2 ≤ D)
    {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
    (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
    (hW : ∀ n x, 0 < W n x)
    (hdata : ∀ᶠ n : ℕ in atTop,
      (∀ x, W n x/(n:ℝ)^B ≤ |U n x|+
        Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(n:ℝ)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+2,
        ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x) ∘
            (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*W n ((chartAt E (A.p i)).symm y))) :
    ∃ L > 0, ∀ᶠ n : ℕ in atTop,
      let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
      let s := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
      (∀ x, 0 < b x ∧ 0 < s x) ∧
      (∀ x, weightedLaplacian g b (U n) x+sphereFrequency n*s x*U n x=0) ∧
      (tsupport (fun x => b x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
      (tsupport (fun x => s x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
      ∃ v : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
        (∀ x, weightedLaplacian g b v x =
          sphereFrequency n*b x^3*v x^5-sphereFrequency n*s x*v x) ∧
        (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
          |s x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
        (∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => s x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P) := by
  classical
  let b := fun n : ℕ => intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
  let s := fun n : ℕ => intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
  let Coeff : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  have hscalar := A.eventually_scalar_exactification (2*(k+1)) B (P+8) D (by omega) hD
    hC U W hU hW hdata
  have hsm : ∀ᶠ n : ℕ in atTop,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n) :=
    hscalar.mono (fun n hn => ⟨hn.1,hn.2.1⟩)
  have hj : ∀ᶠ n : ℕ in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) :=
    hscalar.mono (fun n hn => ⟨hn.2.2.2.2.1,hn.2.2.2.2.2.1⟩)
  have hfactor := A.eventually_positive_factor_of_eventual_jets hd Coeff N P hN b s hsm hj
  obtain ⟨T,hT,hraw⟩ := A.chartJetBound_controls_finite_real_raw tests N
  let L := 1+T+(Fintype.card A.t:ℝ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hTL : T ≤ L := by dsimp [L]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card A.t); linarith
  have hcardL : (Fintype.card A.t:ℝ) ≤ L := by dsimp [L]; linarith
  refine ⟨L,hL,?_⟩
  filter_upwards [hscalar,hj,hfactor,eventually_ge_atTop 1] with n hsc hj hv hn1
  obtain ⟨v,hv,hvpos,hveq,hvj⟩ := hv
  have hni : 0 ≤ inverseFrequency n := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hni1 : inverseFrequency n ≤ 1 := by
    unfold inverseFrequency
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hn1)
  have hpow : inverseFrequency n^(P+8) ≤ inverseFrequency n^P :=
    pow_le_pow_of_le_one hni hni1 (by omega)
  have hbj : A.ChartJetBound N (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^P) :=
    fun i j hjN y => (hj.1 i j (hjN.trans hNP) y).trans hpow
  have hsj : A.ChartJetBound N (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^P) :=
    fun i j hjN y => (hj.2 i j (hjN.trans hNP) y).trans hpow
  have hrawb := hraw (fun x => b n x-1) (hsc.1.sub contMDiff_const)
    _ (pow_nonneg hni _) hbj
  have hraws := hraw (fun x => s n x-1) (hsc.2.1.sub contMDiff_const)
    _ (pow_nonneg hni _) hsj
  have hrawv := hraw (fun x => v x-1) (hv.sub contMDiff_const)
    _ (pow_nonneg hni _) hvj
  refine ⟨hsc.1,hsc.2.1,hsc.2.2.1,hsc.2.2.2.1,
    hsc.2.2.2.2.2.2.2.1,hsc.2.2.2.2.2.2.2.2,v,hv,hvpos,hveq,?_,?_⟩
  · intro x
    have value {f : M → ℝ}
        (hf : A.ChartJetBound N (fun y => ((f y:ℝ):ℂ)) (inverseFrequency n^P)) :
        |f x| ≤ L*inverseFrequency n^P := by
      have hh := A.chartJetBound_global_value (pow_nonneg hni _) hf x
      simp only [Complex.norm_real,Real.norm_eq_abs] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hcardL (pow_nonneg hni _))
    exact ⟨value hbj,value hsj,value hvj⟩
  · intro t ht y hy j hj
    have hbound := mul_le_mul_of_nonneg_right hTL (pow_nonneg hni P)
    exact ⟨(hrawb t ht y hy j hj).trans hbound,
      (hraws t ht y hy j hj).trans hbound,(hrawv t ht y hy j hj).trans hbound⟩
end CompactMetricAtlas
end YauCounterexamples
end


end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw_oai.{u_1, u_2} := @OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_factor_raw_oai.{u_1, u_2}
