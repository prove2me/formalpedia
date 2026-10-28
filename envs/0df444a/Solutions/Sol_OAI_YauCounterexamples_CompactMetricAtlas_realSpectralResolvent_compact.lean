-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:55:00.184534+00:00
-- url     : https://prove2.me/submissions/e466bd7f-0474-49c0-b5f5-8bce3357c74d

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LpNormTwoBounds
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lp_norm_le_two_bounds {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g h : Lp ℂ 2 μ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ a * ‖g x‖ + b * ‖h x‖) :
    ‖f‖ ≤ a * ‖g‖ + b * ‖h‖ := by
  let G : Lp ℝ 2 μ := (Lp.memLp g).norm.toLp (fun x => ‖g x‖)
  let H : Lp ℝ 2 μ := (Lp.memLp h).norm.toLp (fun x => ‖h x‖)
  have hG : ‖G‖ = ‖g‖ := by
    dsimp only [G]
    rw [Lp.norm_toLp, eLpNorm_norm _, Lp.norm_def]
  have hH : ‖H‖ = ‖h‖ := by
    dsimp only [H]
    rw [Lp.norm_toLp, eLpNorm_norm _, Lp.norm_def]
  have hh : ‖f‖ ≤ ‖a • G + b • H‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hf, (Lp.memLp g).norm.coeFn_toLp, (Lp.memLp h).norm.coeFn_toLp,
      Lp.coeFn_add (a • G) (b • H), Lp.coeFn_smul a G, Lp.coeFn_smul b H] with x hx hg hh hs ha' hb'
    rw [hs]
    simp only [Pi.add_apply]
    rw [ha', hb']
    change ‖f x‖ ≤ ‖a * G x + b * H x‖
    change G x = ‖g x‖ at hg
    change H x = ‖h x‖ at hh
    rw [hg, hh, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hx
  exact hh.trans ((norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb, hG, hH]))

lemma power_interpolation {q ε : ℝ} (hq : 1 ≤ q) (hε : 0 < ε) (k : ℕ) :
    q ^ k ≤ ε * q ^ (k + 1) + (ε⁻¹) ^ k := by
  by_cases h : ε⁻¹ ≤ q
  · have he : 1 ≤ ε * q := by
      simpa only [mul_inv_cancel₀ hε.ne.symm] using mul_le_mul_of_nonneg_left h hε.le
    have hmul := mul_le_mul_of_nonneg_right he (pow_nonneg (by linarith : 0 ≤ q) k)
    rw [one_mul] at hmul
    calc
      _ ≤ ε * q ^ (k + 1) := by simpa only [pow_succ] using hmul.trans_eq (by ring)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · have hp := pow_le_pow_left₀ (by linarith : 0 ≤ q) (le_of_not_ge h) k
    exact hp.trans (le_add_of_nonneg_left (by positivity))

lemma norm_schwartz_interpolation (k : ℕ) {ε : ℝ} (hε : 0 < ε) (f : 𝓢(E, ℂ)) :
    ‖schwartzToSobolev (2 * (k : ℝ)) f‖ ≤
      ε * ‖schwartzToSobolev (2 * ((k + 1 : ℕ) : ℝ)) f‖ +
      (ε⁻¹)^k * ‖schwartzToSobolev 0 f‖ := by
  apply lp_norm_le_two_bounds _ _ _ hε.le (by positivity)
  rw [schwartzToSobolev_apply, schwartzToSobolev_apply, schwartzToSobolev_apply]
  filter_upwards [(weightedSchwartz (2 * (k : ℝ)) (𝓕 f)).coeFn_toLp 2 volume,
    (weightedSchwartz (2 * ((k + 1 : ℕ) : ℝ)) (𝓕 f)).coeFn_toLp 2 volume,
    (weightedSchwartz 0 (𝓕 f)).coeFn_toLp 2 volume] with x hx hy hz
  rw [hx, hy, hz, norm_weightedSchwartz, norm_weightedSchwartz, norm_weightedSchwartz]
  simp only [sobolevWeight, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    zero_div, Real.rpow_zero, one_mul, Real.rpow_natCast]
  have hh := mul_le_mul_of_nonneg_right (power_interpolation (by linarith [sq_nonneg ‖x‖] : 1 ≤ 1 + ‖x‖ ^ 2) hε k)
    (norm_nonneg ((𝓕 f) x))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

lemma sobolev_interpolation (k : ℕ) {ε : ℝ} (hε : 0 < ε)
    (u : FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ))) :
    ‖sobolevInclusion _ (2 * (k : ℝ)) (by push_cast; linarith) u‖ ≤
      ε * ‖u‖ + (ε⁻¹)^k * ‖sobolevInclusion _ 0 (by positivity) u‖ := by
  refine (denseRange_schwartzToSobolev _).induction_on u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    simp only [sobolevInclusion_schwartz]
    exact norm_schwartz_interpolation k hε f


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
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma realH_closed (s : ℝ) : IsClosed (A.realH s : Set (A.H s)) := by
  change IsClosed {u | ∀ x, (A.representative s u x).im = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_eq _ continuous_const
  exact Complex.continuous_im.comp ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
    (A.representative s).continuous)

instance realH_completeSpace (s : ℝ) : CompleteSpace (A.realH s) :=
  (A.realH_closed s).completeSpace_coe

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_TotallyBoundedCauchySubsequence
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter
open scoped Topology

lemma totallyBounded_of_cauchy_subsequence {X : Type*} [UniformSpace X] {S : Set X}
    (h : ∀ x : ℕ → X, (∀ n, x n ∈ S) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CauchySeq (x ∘ ψ)) : TotallyBounded S := by
  intro V hV
  contrapose! h
  obtain ⟨u, hu, hdist⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧
      ∀ n m, m < n → u m ∉ UniformSpace.ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and] using! seq_of_forall_finite_exists h
  refine ⟨u, hu, fun ψ hψ hc => ?_⟩
  obtain ⟨N, hN⟩ := hc.mem_entourage hV
  exact hdist (ψ (N + 1)) (ψ N) (hψ (Nat.lt_add_one N))
    (hN (N + 1) N N.le_succ le_rfl)

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma interpolation_cauchy (I : X →L[ℝ] Y) (L : X →L[ℝ] Z)
    (hint : ∀ ε > (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ x, ‖I x‖ ≤ ε * ‖x‖ + D * ‖L x‖)
    (u : ℕ → X) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C)
    (hc : CauchySeq (fun n => L (u n))) : CauchySeq (fun n => I (u n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ := ε / (4 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨D, hD, hDint⟩ := hint δ hδ
  have ht : 0 < ε / (2 * (D + 1)) := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc _ ht
  refine ⟨N, fun n hn m hm => ?_⟩
  have hh := hDint (u n - u m)
  rw [map_sub, map_sub] at hh
  have hu : ‖u n - u m‖ ≤ 2 * C := (norm_sub_le _ _).trans (by linarith [hb n, hb m])
  have hlow := hN n hn m hm
  have hhigh : δ * ‖u n - u m‖ ≤ ε / 2 := by
    have h0 : δ * (2 * C) ≤ ε / 2 := by
      dsimp only [δ]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (C + 1))).mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_left hu hδ.le).trans h0
  have hsmall : D * dist (L (u n)) (L (u m)) < ε / 2 := by
    have hp : 0 < D + 1 := by linarith
    have hlow' := (lt_div_iff₀ (by positivity : 0 < 2 * (D + 1))).mp hlow
    have hz : 0 ≤ dist (L (u n)) (L (u m)) := dist_nonneg
    nlinarith
  rw [dist_eq_norm] at hsmall ⊢
  linarith
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ManifoldSobolevInclusionCoordinate
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma boundedDistribution_memLp (f : E →ᵇ ℂ) (hf : MemLp (f : E → ℂ) 2 volume) :
    boundedDistribution f = Lp.toTemperedDistribution (hf.toLp f) := by
  ext φ
  rw [boundedDistribution_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

lemma sobolev_zero_distribution (u : FourierSobolevSpace E ℂ 0) :
    fourierSobolevDistribution E ℂ 0 u = Lp.toTemperedDistribution (𝓕⁻ u) := by
  rw [fourierSobolevDistribution_apply]
  simp only [neg_zero, zero_div, Real.rpow_zero, Complex.ofReal_one,
    smulLeftCLM_const, one_smul]
  exact Lp.fourierInv_toTemperedDistribution_eq u

lemma sobolev_norm_zero_repr {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) (hu : MemLp (sobolevRepresentative hs u : E → ℂ) 2 volume) :
    ‖sobolevInclusion s 0 (by have _hn : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _; linarith) u‖ =
    ‖hu.toLp (sobolevRepresentative hs u)‖ := by
  let v := sobolevInclusion s 0 (by have _hn : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _; linarith) u
  have he : Lp.toTemperedDistribution (𝓕⁻ v) = Lp.toTemperedDistribution (hu.toLp _) := by
    rw [← sobolev_zero_distribution, sobolevInclusion_distribution,
      ← sobolevRepresentative_distribution hs, boundedDistribution_memLp _ hu]
  have hi : Function.Injective (Lp.toTemperedDistribution (F := ℂ) (p := 2) (μ := (volume : Measure E))) :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  have hh := congrArg norm (hi he)
  have hn := Lp.norm_fourier_eq (𝓕⁻ v)
  rw [fourier_fourierInv_eq] at hn
  exact hn.trans hh

lemma compact_L2_bound (f : E →ᵇ ℂ) (K : Set E) (hK : IsCompact K)
    (hsupp : tsupport f ⊆ K) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    ∃ hf : MemLp (f : E → ℂ) 2 volume,
      ‖hf.toLp f‖ ≤ C * (volume K).toReal ^ (1 / 2 : ℝ) := by
  have hc : HasCompactSupport (f : E → ℂ) := hK.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hf : MemLp (f : E → ℂ) 2 volume :=
    hc.memLp_of_bound f.continuous.aestronglyMeasurable C (Filter.Eventually.of_forall hb)
  refine ⟨hf, ?_⟩
  have he : eLpNorm f 2 volume ≤ ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) := by
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
  rw [Lp.norm_toLp]
  have hfinite : ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hK.measure_lt_top.ne)
  have ht := ENNReal.toReal_mono hfinite he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_rpow] using ht

lemma sobolev_zero_compact_bound {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u : FourierSobolevSpace E ℂ s) (K : Set E) (hK : IsCompact K)
    (hsupp : tsupport (sobolevRepresentative hs u) ⊆ K) :
    ‖sobolevInclusion s 0 (by have _hn : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _; linarith) u‖ ≤
      ‖sobolevRepresentative hs u‖ * (volume K).toReal ^ (1 / 2 : ℝ) := by
  obtain ⟨hf, hh⟩ := compact_L2_bound (sobolevRepresentative hs u) K hK hsupp
    ‖sobolevRepresentative hs u‖ (norm_nonneg _) (fun x => BoundedContinuousFunction.norm_coe_le_norm _ x)
  rw [sobolev_norm_zero_repr hs u hf]
  exact hh

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Metric
open scoped Topology BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E]

lemma supported_bcf_dist_le (K : Set E) (f g : E →ᵇ ℂ)
    (hf : tsupport f ⊆ K) (hg : tsupport g ⊆ K) :
    dist f g ≤ dist (f.domRestrict K) (g.domRestrict K) := by
  apply (BoundedContinuousFunction.dist_le (dist_nonneg)).2
  intro x
  by_cases hx : x ∈ K
  · exact BoundedContinuousFunction.dist_coe_le_dist (f := f.domRestrict K) (g := g.domRestrict K) (⟨x, hx⟩ : K)
  · have hfx : f x = 0 := by
      by_contra hn
      exact hx (hf (subset_tsupport _ hn))
    have hgx : g x = 0 := by
      by_contra hn
      exact hx (hg (subset_tsupport _ hn))
    rw [hfx, hgx, dist_self]
    exact dist_nonneg

theorem supported_bcf_subsequence (K : Set E) (hK : IsCompact K)
    (f : ℕ → E →ᵇ ℂ) (C D : ℝ)
    (hb : ∀ n, ‖f n‖ ≤ C) (hsupp : ∀ n, tsupport (f n) ⊆ K)
    (hlip : ∀ n x y, dist (f n x) (f n y) ≤ D * dist x y) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CauchySeq (f ∘ ψ) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℕ → K →ᵇ ℂ := fun n => (f n).domRestrict K
  have hcomp : IsCompact (closure (Set.range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) C) (isCompact_closedBall _ _)
    · rintro g x ⟨n, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      exact (BoundedContinuousFunction.norm_coe_le_norm (f n) x).trans (hb n)
    · apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => D * t)
        (by
          have hc : Continuous (fun t : ℝ => D * t) := by fun_prop
          simpa only [mul_zero] using hc.tendsto 0)
      rintro x y ⟨g, n, rfl⟩
      exact hlip n x y
  obtain ⟨g, _, ψ, hψ, hg⟩ := hcomp.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨ψ, hψ, Metric.cauchySeq_iff.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hg.cauchySeq ε hε
  exact ⟨N, fun n hn m hm => (supported_bcf_dist_le K (f (ψ n)) (f (ψ m))
    (hsupp _) (hsupp _)).trans_lt (hN n hn m hm)⟩

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolev_repr_dist_bound {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (ht : Module.finrank ℝ E < 2 * (s - 1))
    (u : FourierSobolevSpace E ℂ s) (x y : E) :
    dist (sobolevRepresentative hs u x) (sobolevRepresentative hs u y) ≤
      ((2 * Real.pi * ‖innerSL ℝ (E := E)‖) * ‖momentBesselLp (E := E) (s := s) 1 (by simpa only [Nat.cast_one] using ht)‖ * ‖u‖) * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => ((contDiff_sobolevRepresentative 1 (by simpa only [Nat.cast_one] using ht) hs u).differentiable (by norm_num)) z)
      (fun z _ => ?_) (mem_univ y) (mem_univ x)
  have hh := sobolevRepresentative_jet_bound hs 1 (by simpa only [Nat.cast_one] using ht) u z
  rwa [norm_iteratedFDeriv_one, pow_one] at hh

theorem sobolev_rellich_subsequence (k : ℕ)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ) - 1))
    (K : Set E) (hK : IsCompact K)
    (u : ℕ → FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C)
    (hsupp : ∀ n, tsupport (sobolevRepresentative (by linarith) (u n)) ⊆ K) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CauchySeq (fun n =>
      sobolevInclusion _ (2 * (k : ℝ)) (by push_cast; linarith) (u (ψ n))) := by
  have hs : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by linarith
  let f : ℕ → E →ᵇ ℂ := fun n => sobolevRepresentative hs (u n)
  let D := (2 * Real.pi * ‖innerSL ℝ (E := E)‖) * ‖momentBesselLp (E := E) (s := 2 * ((k + 1 : ℕ) : ℝ)) 1 (by simpa only [Nat.cast_one] using ht)‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨ψ, hψ, hf⟩ := supported_bcf_subsequence K hK f
    (‖sobolevRepresentative hs‖ * C) (D * C)
    (fun n => ((sobolevRepresentative hs).le_opNorm (u n)).trans
      (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _))) hsupp
    (fun n x y => (sobolev_repr_dist_bound hs ht (u n) x y).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb n) hD) dist_nonneg))
  refine ⟨ψ, hψ, ?_⟩
  have hlow : CauchySeq (fun n => sobolevInclusion _ 0 (by positivity) (u (ψ n))) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let V := (volume K).toReal ^ (1 / 2 : ℝ)
    have hV : 0 ≤ V := by positivity
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf (ε / (V + 1)) (div_pos hε (by positivity))
    refine ⟨N, fun n hn m hm => ?_⟩
    have hh := sobolev_zero_compact_bound hs (u (ψ n) - u (ψ m)) K hK (by
      rw [map_sub]
      exact (tsupport_sub _ _).trans (union_subset (hsupp _) (hsupp _)))
    rw [map_sub, map_sub, ← dist_eq_norm, ← dist_eq_norm] at hh
    have hn' := hN n hn m hm
    have hv := (lt_div_iff₀ (by positivity : 0 < V + 1)).mp hn'
    change dist (f (ψ n)) (f (ψ m)) * (V + 1) < ε at hv
    have hz : 0 ≤ dist (f (ψ n)) (f (ψ m)) := dist_nonneg
    change dist _ _ ≤ dist (f (ψ n)) (f (ψ m)) * V at hh
    nlinarith
  exact interpolation_cauchy
    ((sobolevInclusion _ (2 * (k : ℝ)) (by push_cast; linarith)).restrictScalars ℝ)
    ((sobolevInclusion _ 0 (by positivity)).restrictScalars ℝ)
    (fun ε hε => ⟨(ε⁻¹)^k, by positivity, sobolev_interpolation k hε⟩)
    (fun n => u (ψ n)) hC (fun n => hb (ψ n)) hlow

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter
open scoped Topology Manifold BoundedContinuousFunction ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))

omit [CompactSpace M] in
lemma manifoldSobolevInclusion_coordinate (s t : ℝ) (h : t ≤ s)
    (u : ManifoldSobolev p η hηc hηs hηm s) (i : ι) :
    (manifoldSobolevInclusion p η hηc hηs hηm s t u).val i =
      sobolevInclusion s t h (u.val i) := by
  refine (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact (continuous_apply i).comp (continuous_subtype_val.comp
        (manifoldSobolevInclusion p η hηc hηs hηm s t).continuous)
    · exact (sobolevInclusion s t h).continuous.comp
        ((continuous_apply i).comp continuous_subtype_val)
  · intro f
    rw [manifoldSobolevInclusion_smooth p η hηc hηs hηm s t h]
    exact (sobolevInclusion_schwartz s t h _).symm

theorem manifoldSobolevInclusion_compact (hηone : ∀ x, ∑ i, η i x = 1) (k : ℕ)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ) - 1)) :
    IsCompactOperator (manifoldSobolevInclusion p η hηc hηs hηm
      (2 * ((k + 1 : ℕ) : ℝ)) (2 * (k : ℝ))) := by
  classical
  let s : ℝ := 2 * ((k + 1 : ℕ) : ℝ)
  let t : ℝ := 2 * (k : ℝ)
  have hts : t ≤ s := by dsimp [s, t]; push_cast; linarith
  have hs : Module.finrank ℝ E < 2 * s := by dsimp [s]; linarith
  let I := manifoldSobolevInclusion p η hηc hηs hηm s t
  let K : ι → Set E := fun i => (chartAt E (p i)) '' tsupport (η i)
  have hK : ∀ i, IsCompact (K i) := fun i => isCompact_chartSupport (p i) (η i) (hηc i) (hηs i)
  let S : ι → Set (FourierSobolevSpace E ℂ t) := fun i =>
    sobolevInclusion s t hts '' {v : FourierSobolevSpace E ℂ s |
      ‖v‖ ≤ 1 ∧ tsupport (sobolevRepresentative hs v) ⊆ K i}
  have hS : ∀ i, TotallyBounded (S i) := by
    intro i
    apply totallyBounded_of_cauchy_subsequence
    intro x hx
    choose u hu he using hx
    obtain ⟨ψ, hψ, hc⟩ := sobolev_rellich_subsequence k ht (K i) (hK i) u 1
      zero_le_one (fun n => (hu n).1) (fun n => (hu n).2)
    refine ⟨ψ, hψ, ?_⟩
    change CauchySeq (fun n => sobolevInclusion s t hts (u (ψ n))) at hc
    simp_rw [he] at hc
    exact hc
  have hc : IsCompact {v : ι → FourierSobolevSpace E ℂ t | ∀ i, v i ∈ closure (S i)} :=
    isCompact_pi_infinite fun i => (hS i).closure.isCompact_of_isClosed isClosed_closure
  have himg : TotallyBounded (Subtype.val '' (I '' Metric.closedBall 0 1)) := by
    apply hc.totallyBounded.subset
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩ i
    apply subset_closure
    refine ⟨u.val i, ⟨?_, ?_⟩, ?_⟩
    · apply (norm_le_pi_norm u.val i).trans
      have hh : ‖u‖ ≤ (1 : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
      convert hh using 1 <;> first | rfl | simp
    · have he : (sobolevRepresentative hs (u.val i) : E → ℂ) =
          chartLocalize (E := E) (p i) (η i)
            (manifoldSobolevRepresentative p η hηc hηs hηm s u) := by
        funext y
        exact manifoldSobolevRepresentative_localize p η hηc hηs hηm hηone hs u i y
      rw [he]
      exact closure_minimal (support_chartLocalize (p i) (η i) _) (hK i).isClosed
    · exact (manifoldSobolevInclusion_coordinate p η hηc hηs hηm s t hts u i).symm
  have himg' : TotallyBounded (I '' Metric.closedBall 0 1) :=
    (totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing).mp himg
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall I.toLinearMap
    (by norm_num : (0 : ℝ) < 1)).mpr (himg'.closure.isCompact_of_isClosed isClosed_closure)


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SpectralResolvent
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem spectralResolvent_compact (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) : IsCompactOperator (A.spectralResolvent B α hα he) := by
  apply (manifoldSobolevInclusion_compact A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η k ?_).comp_clm
  push_cast
  linarith
end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ContinuousEigenpairLinearization
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
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

lemma realSpectralResolvent_compact_oai (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) :
    IsCompactOperator (A.realSpectralResolvent B α hα0 hα he) := by
  have hc := A.spectralResolvent_compact B α hα he
  have hr : ∀ u ∈ A.realH (2 * (k : ℝ)), A.spectralResolvent B α hα he u ∈ A.realH (2 * (k : ℝ)) := by
    intro u hu x
    change (A.representative _ (A.inclusion (A.resolvent B α hα he u)) x).im = 0
    rw [A.inclusion_representative]
    exact A.resolvent_mem_realH B α hα0 hα he ⟨u, hu⟩ x
  exact hc.restrict' hr
end CompactMetricAtlas

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology


end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact_oai.{u_1, u_2} := @OAI.YauCounterexamples.CompactMetricAtlas.realSpectralResolvent_compact_oai.{u_1, u_2}
