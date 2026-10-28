-- Prove2me | solution 1 for OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM_pinned_deriv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:56:54.359879+00:00
-- url     : https://prove2.me/submissions/1357c98f-abe0-455a-8a2d-8da74ba8dc5c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ClmMatrixAlgHom
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma hasDerivAt_det_exp_smul (K : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • K)).det)
      ((NormedSpace.exp (t • K)).det * K.trace) t := by
  have hu : IsUnit (NormedSpace.exp (t • K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (NormedSpace.isUnit_exp (t • K))
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) K t
  have hd := (differentiable_det (NormedSpace.exp (t • K))).hasFDerivAt.comp_hasDerivAt t he
  erw [fderiv_det_apply _ _ hu,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.mul_one] at hd
  exact hd

theorem matrix_det_exp (K : Matrix ι ι ℝ) :
    (NormedSpace.exp K).det = Real.exp K.trace := by
  let f : ℝ → ℝ := fun t => (NormedSpace.exp (t • K)).det * Real.exp (-t * K.trace)
  have hf (t : ℝ) : HasDerivAt f 0 t := by
    have hh := (hasDerivAt_det_exp_smul K t).mul
      (((hasDerivAt_id t).neg.mul_const K.trace).exp)
    convert hh using 1 <;> first | rfl | ring
  have hc := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt)
    (fun t => (hf t).deriv) 1 0
  have hfe : (NormedSpace.exp K).det * Real.exp (-K.trace) = 1 := by
    simpa only [f,one_smul,neg_mul,one_mul,zero_smul,NormedSpace.exp_zero,Matrix.det_one,
      neg_zero,zero_mul,Real.exp_zero,mul_one] using hc
  calc (NormedSpace.exp K).det =
      (NormedSpace.exp K).det * (Real.exp (-K.trace) * Real.exp K.trace) := by
        rw [← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
    _ = Real.exp K.trace := by rw [← mul_assoc,hfe,one_mul]

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open scoped Matrix.Norms.Operator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma clmMatrix_exp (b : Module.Basis ι ℝ E) (K : E →L[ℝ] E) :
    LinearMap.toMatrix b b (NormedSpace.exp K).toLinearMap =
      NormedSpace.exp (LinearMap.toMatrix b b K.toLinearMap) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  exact NormedSpace.map_exp (clmMatrixAlgHom b)
    (clmMatrixAlgHom b).toLinearMap.continuous_of_finiteDimensional K

lemma clm_det_exp (b : Module.Basis ι ℝ E) (K : E →L[ℝ] E) :
    LinearMap.det (NormedSpace.exp K).toLinearMap =
      Real.exp (LinearMap.trace ℝ E K.toLinearMap) := by
  rw [← LinearMap.det_toMatrix b,clmMatrix_exp b K,matrix_det_exp,
    LinearMap.trace_eq_matrix_trace ℝ b]

omit [FiniteDimensional ℝ E] in
lemma matrixOfForm_pullback (b : Module.Basis ι ℝ E) (G : E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E) :
    matrixOfForm b ((D.precomp ℝ).comp (G.comp D)) =
      (clmMatrixAlgHom b D).transpose * matrixOfForm b G * clmMatrixAlgHom b D := by
  ext i j
  change G (D (b i)) (D (b j)) =
    ((LinearMap.toMatrix b b D.toLinearMap).transpose * matrixOfForm b G *
      LinearMap.toMatrix b b D.toLinearMap) i j
  conv_lhs => arg 1; rw [← b.sum_repr (D (b i))]
  conv_lhs => arg 2; rw [← b.sum_repr (D (b j))]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,matrixOfForm,
    LinearMap.toMatrix_apply,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  change (b.repr (D (b j))) k * ((b.repr (D (b i))) l * G (b l) (b k)) =
    (b.repr (D (b i))) l * G (b l) (b k) * (b.repr (D (b j))) k
  ring

theorem tracefree_exp_preserves_gram_det (b : Module.Basis ι ℝ E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (htr : LinearMap.trace ℝ E K.toLinearMap = 0) :
    (matrixOfForm b (((NormedSpace.exp K).precomp ℝ).comp
      (G.comp (NormedSpace.exp K)))).det = (matrixOfForm b G).det := by
  rw [matrixOfForm_pullback,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  have hd : (clmMatrixAlgHom b (NormedSpace.exp K)).det = 1 := by
    change (LinearMap.toMatrix b b (NormedSpace.exp K).toLinearMap).det = 1
    rw [LinearMap.det_toMatrix,clm_det_exp b K,htr,Real.exp_zero]
  rw [hd,one_mul,mul_one]


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_DerivExpSmulZero
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma hasDerivAt_exp_smul_zero (K : E →L[ℝ] E) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • K)) K 0 := by
  simpa only [zero_smul,NormedSpace.exp_zero,one_mul] using
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) K 0)

lemma exp_smul_apply_deriv_zero (K : E →L[ℝ] E) (v : E) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • K)) v) (K v) 0 := by
  exact (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_smul_zero K)

lemma clm_exp_selfAdjoint (G : E →L[ℝ] E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (hK : ∀ v w, G (K v) w = G v (K w)) (v w : E) :
    G ((NormedSpace.exp K) v) w = G v ((NormedSpace.exp K) w) := by
  have hp (n : ℕ) : ∀ v w, G ((K^n) v) w = G v ((K^n) w) := by
    induction n with
    | zero => intro v w; simp
    | succ n ih =>
      intro v w
      calc G ((K^(n+1)) v) w = G (K ((K^n) v)) w := by rw [pow_succ',mul_apply_eq_comp]
        _ = G ((K^n) v) (K w) := hK _ _
        _ = G v ((K^n) (K w)) := ih _ _
        _ = G v ((K^(n+1)) w) := by rw [pow_succ,mul_apply_eq_comp]
  let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    (G.flip w).comp (ContinuousLinearMap.apply ℝ E v) -
      (G v).comp (ContinuousLinearMap.apply ℝ E w)
  have hL (n : ℕ) : L (K^n) = 0 := sub_eq_zero.mpr (hp n v w)
  have he : L (NormedSpace.exp K) = 0 := by
    rw [NormedSpace.exp_eq_tsum ℝ,L.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℝ) K)]
    simp only [map_smul,hL,smul_zero,tsum_zero]
  exact sub_eq_zero.mp he

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_UniformDifferenceQuotient
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology BoundedContinuousFunction
namespace YauCounterexamples
variable {X F : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_difference_quotient (f d : ℝ → X → F)
    (hd : Continuous (fun z : ℝ × X => d z.1 z.2))
    (hf : ∀ t x, HasDerivAt (fun r => f r x) (d t x) t) :
    TendstoUniformly (fun t x => t⁻¹ • (f t x-f 0 x)) (d 0) (𝓝[≠] (0 : ℝ)) := by
  let : UniformSpace X := uniformSpaceOfCompactR1
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hu := Continuous.tendstoUniformly d hd 0
  have he := (Metric.tendstoUniformly_iff.mp hu) (ε/2) (by positivity)
  obtain ⟨δ,hδ,hδe⟩ := Metric.mem_nhds_iff.mp he
  have htball : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Metric.ball 0 δ := Metric.ball_mem_nhds 0 hδ
  have ht : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∈ Metric.ball 0 δ ∧ t ≠ 0 :=
    (htball.filter_mono nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
  filter_upwards [ht] with t ht
  intro x
  have hder (r : ℝ) : HasDerivAt (fun r => f r x-r • d 0 x) (d r x-d 0 x) r := by
    simpa only [id_eq,one_smul,Pi.sub_apply] using! (hf r x).sub ((hasDerivAt_id r).smul_const (d 0 x))
  have hb (r : ℝ) (hr : r ∈ Metric.ball 0 δ) : ‖d r x-d 0 x‖ ≤ ε/2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hδe hr x).le
  have hm := (convex_ball (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hder r).hasDerivWithinAt) hb (Metric.mem_ball_self hδ) ht.1
  have hm' : ‖f t x-f 0 x-t • d 0 x‖ ≤ (ε/2)*‖t‖ := by
    simpa only [zero_smul, sub_zero, sub_right_comm] using hm
  have heq : t⁻¹ • (f t x-f 0 x)-d 0 x =
      t⁻¹ • (f t x-f 0 x-t • d 0 x) := by
    symm
    rw [smul_sub,smul_smul,inv_mul_cancel₀ ht.2,one_smul]
  rw [dist_eq_norm,norm_sub_rev,heq,norm_smul]
  calc
    ‖t⁻¹‖ * ‖f t x-f 0 x-t • d 0 x‖ ≤ ‖t⁻¹‖*((ε/2)*‖t‖) :=
      mul_le_mul_of_nonneg_left hm' (norm_nonneg _)
    _ = (ε/2)*(‖t‖⁻¹*‖t‖) := by rw [norm_inv]; ring
    _ = ε/2 := by rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht.2),mul_one]
    _ < ε := half_lt_self hε

theorem bounded_difference_quotient (f d : ℝ → X →ᵇ F)
    (hd : Continuous (fun z : ℝ × X => d z.1 z.2))
    (hf : ∀ t x, HasDerivAt (fun r => f r x) (d t x) t) :
    Tendsto (fun t => t⁻¹ • (f t-f 0)) (𝓝[≠] (0 : ℝ)) (𝓝 (d 0)) := by
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
  exact uniform_difference_quotient (fun t x => f t x) (fun t x => d t x) hd hf
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_LocalIntegrationParts
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
section LocalIBP
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma local_integration_by_parts {O : Set E} (hO : IsOpen O)
    {f F : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ O) (hF : ContDiffOn ℝ ∞ F O) (v : E) :
    (∫ x in O, f x * fderiv ℝ F x v) = -(∫ x in O, fderiv ℝ f x v * F x) := by
  obtain ⟨H, hH, he⟩ := smooth_extension_near_compact hfc hO hfs hF
  have he' (x : E) (hx : x ∈ tsupport f) : F =ᶠ[𝓝 x] H :=
    he.filter_mono (nhds_le_nhdsSet hx)
  have hdf := (hf.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := v))
  have hdH := (hH.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := v))
  have h1 (x : E) : f x * fderiv ℝ F x v = f x * fderiv ℝ H x v := by
    by_cases hx : x ∈ tsupport f
    · rw [(he' x hx).fderiv_eq]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have h2 (x : E) : fderiv ℝ f x v * F x = fderiv ℝ f x v * H x := by
    by_cases hx : x ∈ tsupport f
    · rw [(he' x hx).eq_of_nhds]
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  simp_rw [h1, h2]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (mt (@hfs x) hx), zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [fderiv_of_notMem_tsupport ℝ (mt (@hfs x) hx)]; simp)]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hdf.continuous.mul hH.continuous |>.integrable_of_hasCompactSupport
      ((hfc.fderiv_apply ℝ v).mul_right))
    (hf.continuous.mul hdH.continuous |>.integrable_of_hasCompactSupport hfc.mul_right)
    (hf.continuous.mul hH.continuous |>.integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
    (fun x _ => (hH.differentiable (by simp)).differentiableAt)
end LocalIBP

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma realChartLocalize_eq (p : M) (u : M → ℝ) {y : E} (hy : y ∈ (chartAt E p).target) :
    realChartLocalize (E := E) p u y = u ((chartAt E p).symm y) := ite_eq_left hy

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma support_realChartLocalize (p : M) (u : M → ℝ) :
    support (realChartLocalize (E := E) p u) ⊆ (chartAt E p) '' tsupport u := by
  intro y hy
  by_cases hy' : y ∈ (chartAt E p).target
  · refine ⟨(chartAt E p).symm y, ?_, (chartAt E p).right_inv hy'⟩
    apply subset_tsupport
    change u ((chartAt E p).symm y) ≠ 0
    change realChartLocalize (E := E) p u y ≠ 0 at hy
    simpa only [realChartLocalize, ite_eq_left hy'] using hy
  · exact False.elim (hy (by simp only [realChartLocalize, ite_eq_right hy']))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma isCompact_realChartSupport (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    IsCompact ((chartAt E p) '' tsupport u) :=
  hc.image_of_continuousOn ((chartAt E p).continuousOn.mono hs)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma tsupport_realChartLocalize (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    tsupport (realChartLocalize (E := E) p u) ⊆ (chartAt E p) '' tsupport u :=
  closure_minimal (support_realChartLocalize p u) (isCompact_realChartSupport p u hc hs).isClosed

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma hasCompactSupport_realChartLocalize (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    HasCompactSupport (realChartLocalize (E := E) p u) :=
  (isCompact_realChartSupport p u hc hs).of_isClosed_subset isClosed_closure
    (tsupport_realChartLocalize p u hc hs)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma tsupport_realChartLocalize_subset (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    tsupport (realChartLocalize (E := E) p u) ⊆ (chartAt E p).target :=
  (tsupport_realChartLocalize p u hc hs).trans
    (image_subset_iff.mpr fun _ hx => (chartAt E p).map_source (hs hx))

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiff_realChartLocalize (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞ (realChartLocalize (E := E) p u) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro y hy
  have hyt := tsupport_realChartLocalize_subset (E := E) p u hc hs hy
  have hh := contDiffAt_inChart hu p hyt
  rw [contMDiffAt_iff_contDiffAt]
  apply hh.congr_of_eventuallyEq
  filter_upwards [(chartAt E p).open_target.mem_nhds hyt] with z hz
  exact realChartLocalize_eq p u hz

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma realChartLocalize_fderiv (p : M) (u : M → ℝ) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    fderiv ℝ (realChartLocalize (E := E) p u) y = fderiv ℝ (u ∘ (chartAt E p).symm) y := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
  exact realChartLocalize_eq p u hz


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoefficientGradientApply
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

lemma metricChartIntegral_change (g : SmoothMetric E M) (p q : M) (f : M → ℝ)
    (hp : support f ⊆ (chartAt E p).source)
    (hq : support f ⊆ (chartAt E q).source) :
    metricChartIntegral g p f = metricChartIntegral g q f := by
  let e := (chartAt E q).symm.trans (chartAt E p)
  have hs : e.source ⊆ (chartAt E q).target := fun _ h => h.1
  have ht : e.target ⊆ (chartAt E p).target := fun _ h => h.1
  have hleft : metricChartIntegral g p f =
      ∫ y in e.target, Real.sqrt (metricCoefficients g p y).det * f ((chartAt E p).symm y) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (chartAt E p).open_target.measurableSet ht
    intro y hy
    have hz : f ((chartAt E p).symm y) = 0 := by
      by_contra hh
      exact hy.2 ⟨hy.1, hq hh⟩
    rw [hz, mul_zero]
  have hright : metricChartIntegral g q f =
      ∫ y in e.source, Real.sqrt (metricCoefficients g q y).det * f ((chartAt E q).symm y) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (chartAt E q).open_target.measurableSet hs
    intro y hy
    have hz : f ((chartAt E q).symm y) = 0 := by
      by_contra hh
      exact hy.2 ⟨hy.1, hp hh⟩
    rw [hz, mul_zero]
  rw [hleft, hright]
  have hd : ∀ y ∈ e.source, HasFDerivAt e (fderiv ℝ (chartTransition p q) y) y := by
    intro y hy
    exact ((contDiffAt_chartTransition p q hy.1 hy.2).differentiableAt (by simp)).hasFDerivAt
  rw [integral_target_eq_integral_abs_det_fderiv_smul volume hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro y hy
  dsimp only
  rw [metricDensity_change g p q hy.1 hy.2]
  have he : (chartAt E p).symm (e y) = (chartAt E q).symm y :=
    (chartAt E p).left_inv hy.2
  rw [he]
  change |(fderiv ℝ (chartTransition p q) y).toLinearMap.det| *
    (Real.sqrt (metricCoefficients g p (chartTransition p q y)).det * _) = _
  rw [coordinateTransitionMatrix, LinearMap.det_toMatrix]
  ring

end

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

namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

omit [T2Space M] in
lemma integral_eq_chart (q : M) (f : M →ᵇ ℝ)
    (hf : tsupport f ⊆ (chartAt E q).source) :
    A.integral g f = metricChartIntegral g q f := by
  classical
  have hc (i : A.t) : IntegrableOn (fun y => Real.sqrt (metricCoefficients g q y).det *
      (A.ρ i ((chartAt E q).symm y) * f ((chartAt E q).symm y))) (chartAt E q).target :=
    metricChart_integrable g q ((A.ρ i).property.continuous.mul f.continuous)
      (HasCompactSupport.of_compactSpace _) (tsupport_mul_subset_right.trans hf)
  unfold integral
  calc
    _ = ∑ i : A.t, metricChartIntegral g q (fun x => A.ρ i x * f x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply metricChartIntegral_change
      · exact (subset_tsupport _).trans (tsupport_mul_subset_left.trans (A.subordinate i))
      · exact (subset_tsupport _).trans (tsupport_mul_subset_right.trans hf)
    _ = ∫ y in (chartAt E q).target, ∑ i : A.t,
        Real.sqrt (metricCoefficients g q y).det * (A.ρ i ((chartAt E q).symm y) *
          f ((chartAt E q).symm y)) := (integral_finsetSum _ (fun i _ => hc i)).symm
    _ = metricChartIntegral g q f := by
      apply setIntegral_congr_fun (chartAt E q).open_target.measurableSet
      intro y _
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      have hρ : ∑ i : A.t, A.ρ i ((chartAt E q).symm y) = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using A.ρ.sum_eq_one (mem_univ ((chartAt E q).symm y))
      rw [hρ, one_mul]

end MetricIntegralAtlas

end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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
section ProductCalculus
variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike 𝕜]
lemma second_fderiv_mul_at {u v : E → 𝕜} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z * v z) y b) x a =
      u x * fderiv ℝ (fun y => fderiv ℝ v y b) x a +
      v x * fderiv ℝ (fun y => fderiv ℝ u y b) x a +
      fderiv ℝ u x a * fderiv ℝ v x b +
      fderiv ℝ u x b * fderiv ℝ v x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hdv := hv.differentiableAt (by norm_num)
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have hdv' : DifferentiableAt ℝ (fun y => fderiv ℝ v y b) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (fun z => u z * v z) y b) =ᶠ[𝓝 x]
      (fun y => u y * fderiv ℝ v y b + v y * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hy hz
    rw [fderiv_fun_mul (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [he.fderiv_eq]
  erw [fderiv_fun_add (hdu.mul hdv') (hdv.mul hdu'),
    fderiv_fun_mul hdu hdv', fderiv_fun_mul hdv hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring
end ProductCalculus
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_mul {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y * v y) x =
      u x * laplaceBeltrami g v x + v x * laplaceBeltrami g u x +
        2 * coordinateGradientPair g u v x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hv' := contDiffAt_inChart_C2 hv x hx
  change localLaplacian g _ x (c x) = _
  have huv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (fun y => u y * v y) := hu.mul hv
  rw [localLaplacian_expansion_C2 huv g x hx]
  change _ = u x * localLaplacian g v x (c x) +
    v x * localLaplacian g u x (c x) + 2 * coordinateGradientPair g u v x
  rw [localLaplacian_expansion_C2 hu g x hx, localLaplacian_expansion_C2 hv g x hx]
  have hs (i j : CoordIndex E) : (metricCoefficients g x (c x))⁻¹ j i =
      (metricCoefficients g x (c x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x hx).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hcross : (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i)) =
      coordinateGradientPair g u v x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) y (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) *
        fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) = _
  have hd1 (j : CoordIndex E) :
      fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) =
        u x * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
        v x * fderiv ℝ (u ∘ c.symm) (c x) (b j) := by
    erw [fderiv_fun_mul (hu'.differentiableAt (by norm_num))
      (hv'.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z)
        y (b j)) (c x) (b i) =
      u x * fderiv ℝ (fun y => fderiv ℝ (v ∘ c.symm) y (b j)) (c x) (b i) +
      v x * fderiv ℝ (fun y => fderiv ℝ (u ∘ c.symm) y (b j)) (c x) (b i) +
      fderiv ℝ (u ∘ c.symm) (c x) (b i) * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i) := by
    have he := second_fderiv_mul_at hu' hv' (b i) (b j)
    dsimp only [c] at hinv he ⊢
    simpa only [Function.comp_apply, hinv] using he
  simp_rw [hd2, hd1]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc, hcross]
  unfold coordinateGradientPair
  dsimp only [c, b]
  simp only [← Finset.mul_sum, mul_assoc, mul_left_comm]
  ring


end

open Set Filter Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_JointLocalLaplacian
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
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

lemma contDiffAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply hd.mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart hu p hy).fderiv_right (m := ∞) (by simp)
  exact ha.mul (hv.clm_apply contDiffAt_const)

lemma contDiffAt_localLaplacian {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (localLaplacian g u p) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_metricFlux hu g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma contMDiff_laplaceBeltrami {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (laplaceBeltrami g u) := by
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (contDiffAt_localLaplacian hu g x hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := laplaceBeltrami_inChart hu g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
include hq hu

lemma hasDerivAt_laplaceBeltrami_time (t : ℝ) (p : M) :
    HasDerivAt (fun r => laplaceBeltrami (q r) u p)
      (deriv (fun r => laplaceBeltrami (q r) u p) t) t := by
  have hh := (joint_laplaceBeltrami_chart q hq hu t p ((chartAt E p).map_source (mem_chart_source E p))).comp t
    (show ContDiffAt ℝ ∞ (fun r : ℝ => (r,chartAt E p p)) t from contDiffAt_id.prodMk contDiffAt_const)
  have hf : ContDiffAt ℝ ∞ (fun r => laplaceBeltrami (q r) u p) t := by
    simpa only [Function.comp_def, (chartAt E p).left_inv (mem_chart_source E p)] using hh
  exact (hf.differentiableAt (by simp)).hasDerivAt

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
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
open Set Filter Manifold
open scoped Topology ContDiff Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contMDiff_coordinateGradientPair {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (coordinateGradientPair g u v) := by
  have he : coordinateGradientPair g u v = fun x => (2 : ℝ)⁻¹ *
      (laplaceBeltrami g (fun y => u y * v y) x -
        u x * laplaceBeltrami g v x - v x * laplaceBeltrami g u x) := by
    funext x
    rw [laplaceBeltrami_mul (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    ring
  rw [he]
  exact contMDiff_const.mul (((contMDiff_laplaceBeltrami (hu.mul hv) g).sub
    (hu.mul (contMDiff_laplaceBeltrami hv g))).sub (hv.mul (contMDiff_laplaceBeltrami hu g)))

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_IntegrableCompactTsupport
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
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma integrableOn_compact_tsupport {O : Set E} (hO : IsOpen O) {f : E → ℝ}
    (hf : ContinuousOn f O) (hc : HasCompactSupport f) (hs : tsupport f ⊆ O) :
    IntegrableOn f O := by
  apply IntegrableOn.of_inter_support hO.measurableSet
  exact ((hf.mono hs).integrableOn_compact hc).mono_set (fun _ hx => subset_tsupport f hx.2)

omit [T2Space M] in

theorem metricChartIntegral_green (g : SmoothMetric E M) (p : M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v)
    (huc : HasCompactSupport u) (hus : tsupport u ⊆ (chartAt E p).source) :
    metricChartIntegral g p (fun x => u x * laplaceBeltrami g v x) =
      -metricChartIntegral g p (coordinateGradientPair g u v) := by
  let f := realChartLocalize (E := E) p u
  let O := (chartAt E p).target
  let b := Module.finBasis ℝ E
  have hf : ContDiff ℝ ∞ f := contDiff_realChartLocalize p u huc hus hu
  have hfc : HasCompactSupport f := hasCompactSupport_realChartLocalize p u huc hus
  have hfs : tsupport f ⊆ O := tsupport_realChartLocalize_subset p u huc hus
  have hflux (i : CoordIndex E) : ContDiffOn ℝ ∞ (fun y => metricFlux g v p y i) O :=
    fun y hy => (contDiffAt_metricFlux hv g p hy i).contDiffWithinAt
  have hdf (i : CoordIndex E) : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (b i)) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hFi (i : CoordIndex E) : IntegrableOn (fun y => f y *
      fderiv ℝ (fun z => metricFlux g v p z i) y (b i)) O := by
    apply integrableOn_compact_tsupport (chartAt E p).open_target
    · apply hf.continuous.continuousOn.mul
      intro y hy
      exact (((contDiffAt_metricFlux hv g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply
        contDiffAt_const).continuousAt.continuousWithinAt
    · exact hfc.mul_right
    · exact tsupport_mul_subset_left.trans hfs
  have hGi (i : CoordIndex E) : IntegrableOn (fun y => fderiv ℝ f y (b i) * metricFlux g v p y i) O := by
    apply integrableOn_compact_tsupport (chartAt E p).open_target
    · exact (hdf i).continuous.continuousOn.mul (hflux i).continuousOn
    · exact (hfc.fderiv_apply ℝ (b i)).mul_right
    · exact tsupport_mul_subset_left.trans ((tsupport_fderiv_apply_subset ℝ (b i)).trans hfs)
  have hleft : metricChartIntegral g p (fun x => u x * laplaceBeltrami g v x) =
      ∫ y in O, ∑ i, f y * fderiv ℝ (fun z => metricFlux g v p z i) y (b i) := by
    apply setIntegral_congr_fun (chartAt E p).open_target.measurableSet
    intro y hy
    dsimp only
    rw [laplaceBeltrami_inChart hv g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy]
    simp only [localLaplacian, ← Finset.mul_sum]
    rw [show f y = u ((chartAt E p).symm y) from realChartLocalize_eq p u hy]
    have hd : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
      (Real.sqrt_pos.2 (metricCoefficients_posDef g p hy).det_pos).ne'
    dsimp only [b]
    field_simp
  have hright : metricChartIntegral g p (coordinateGradientPair g u v) =
      ∫ y in O, ∑ i, fderiv ℝ f y (b i) * metricFlux g v p y i := by
    apply setIntegral_congr_fun (chartAt E p).open_target.measurableSet
    intro y hy
    dsimp only
    rw [coordinateGradientPair_inChart hu hv g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy]
    dsimp only [f]
    rw [realChartLocalize_fderiv p u hy]
    simp only [localGradientPair, metricFlux, Matrix.mulVec, dotProduct, Finset.mul_sum, b]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  rw [hleft, hright, integral_finsetSum _ (fun i _ => hFi i),
    integral_finsetSum _ (fun i _ => hGi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact local_integration_by_parts (chartAt E p).open_target hf hfc hfs (hflux i) (b i)
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_CoordinateGradientPairScalarCorrection
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
section GradientPairCalculus
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_zero_off_support (g : SmoothMetric E M) (u v : M → ℝ)
    {x : M} (hx : x ∉ tsupport u) : coordinateGradientPair g u v x = 0 := by
  have hzero : u =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have hc : Tendsto (chartAt E x).symm (𝓝 ((chartAt E x) x)) (𝓝 x) := by
    have hh := (chartAt E x).continuousOn_symm.continuousAt
      ((chartAt E x).open_target.mem_nhds ((chartAt E x).map_source (mem_chart_source E x)))
    simpa only [ContinuousAt, (chartAt E x).left_inv (mem_chart_source E x)] using hh
  have he : (u ∘ (chartAt E x).symm) =ᶠ[𝓝 ((chartAt E x) x)] (fun _ => (0 : ℝ)) :=
    hzero.comp_tendsto hc
  simp only [coordinateGradientPair, he.fderiv_eq, fderiv_const_apply, _root_.zero_apply,
    mul_zero, zero_mul, Finset.sum_const_zero]

lemma tsupport_coordinateGradientPair_left (g : SmoothMetric E M) (u v : M → ℝ) :
    tsupport (coordinateGradientPair g u v) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (coordinateGradientPair_zero_off_support g u v hn)

lemma coordinateGradientPair_fintype_sum {ι : Type*} [Fintype ι]
    (g : SmoothMetric E M) (f : ι → M → ℝ)
    (hf : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f a)) (v : M → ℝ) (x : M) :
    coordinateGradientPair g (fun y => ∑ a, f a y) v x =
      ∑ a, coordinateGradientPair g (f a) v x := by
  have hd : fderiv ℝ ((fun y => ∑ a, f a y) ∘ (chartAt E x).symm) ((chartAt E x) x) =
      ∑ a, fderiv ℝ (f a ∘ (chartAt E x).symm) ((chartAt E x) x) :=
    fderiv_fun_sum (fun a _ => (contDiffAt_inChart (hf a) x
      ((chartAt E x).map_source (mem_chart_source E x))).differentiableAt (by simp))
  simp only [coordinateGradientPair, hd, _root_.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ a : ι, ∑ j, (metricCoefficients g x ((chartAt E x) x))⁻¹ i j *
        fderiv ℝ (f a ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i) *
        fderiv ℝ (v ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm
end GradientPairCalculus

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
   [CompactSpace M]
namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

lemma mean_fintype_sum {ι : Type*} [Fintype ι] (f : ι → M → ℝ)
    (hf : ∀ i, Continuous (f i)) : A.mean g (fun x => ∑ i, f i x) = ∑ i, A.mean g (f i) := by
  let F (i : ι) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f i,hf i⟩
  have he : (fun x => ∑ i, f i x) = (⇑(∑ i, F i)) := by funext x; simp [F]
  rw [he]
  change A.integralCLM g (∑ i, F i) = _
  rw [map_sum]
  rfl

lemma mean_eq_chart (p : M) (f : M → ℝ) (hf : Continuous f)
    (hs : tsupport f ⊆ (chartAt E p).source) : A.mean g f = metricChartIntegral g p f :=
  A.integral_eq_chart g p (BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩) hs

theorem green {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) :
    A.mean g (fun x => u x * laplaceBeltrami g v x) =
      -A.mean g (coordinateGradientPair g u v) := by
  let f (i : A.t) (x : M) := A.ρ i x * u x
  have hf (i : A.t) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f i) := (A.ρ i).property.mul hu
  have hs (i : A.t) : tsupport (f i) ⊆ (chartAt E (i : M)).source :=
    tsupport_mul_subset_left.trans (A.subordinate i)
  have hsum : (fun x => ∑ i : A.t, f i x) = u := by
    funext x
    dsimp only [f]
    rw [← Finset.sum_mul]
    have hρ : ∑ i : A.t, A.ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using A.ρ.sum_eq_one (mem_univ x)
    rw [hρ, one_mul]
  calc
    _ = ∑ i : A.t, metricChartIntegral g (i : M) (fun x => f i x * laplaceBeltrami g v x) := by
      unfold mean
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      funext x
      dsimp [f]
      ring
    _ = -(∑ i : A.t, metricChartIntegral g (i : M) (coordinateGradientPair g (f i) v)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact metricChartIntegral_green g _ (hf i) hv (HasCompactSupport.of_compactSpace _) (hs i)
    _ = -(∑ i : A.t, A.mean g (coordinateGradientPair g (f i) v)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (A.mean_eq_chart g (i : M) _ (contMDiff_coordinateGradientPair (hf i) hv g).continuous
        ((tsupport_coordinateGradientPair_left g (f i) v).trans (hs i))).symm
    _ = -A.mean g (coordinateGradientPair g u v) := by
      rw [← A.mean_fintype_sum g _ (fun i => (contMDiff_coordinateGradientPair (hf i) hv g).continuous)]
      congr 2
      funext x
      rw [← coordinateGradientPair_fintype_sum g f hf v x, hsum]

end MetricIntegralAtlas

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



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_PinnedMetricJointGradientPair
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
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma pinnedMetric_inner (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x))) (t : ℝ)
    (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    (pinnedMetric g K hK t).inner x v w =
      g.inner x ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) v)
        ((NormedSpace.exp ((-t/2) • (show E →L[ℝ] E from K x))) w) := rfl


end


section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma pinnedMetric_det (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) ((𝓘(ℝ,E)).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    (t : ℝ) (p : M) (y : E) (hy : y ∈ (chartAt E p).target) :
    (metricCoefficients (pinnedMetric g K hK t) p y).det =
      (metricCoefficients g p y).det := by
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner ((chartAt E p).symm y)
  let A : E →L[ℝ] E := K ((chartAt E p).symm y)
  have ht : LinearMap.trace ℝ E (((-t/2) • A).toLinearMap) = 0 := by
    change LinearMap.trace ℝ E ((-t/2) • A.toLinearMap) = 0
    rw [map_smul,htr,smul_zero]
  exact tracefree_exp_preserves_gram_det (chartTangentBasis p y hy) G ((-t/2) • A) ht


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter NormedSpace
open scoped Topology
open scoped Matrix.Norms.Operator
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff Matrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma metricGradient_coordinate_pairing (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) (y : E)
    (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    g.inner ((chartAt E p).symm y) (metricGradient g u ((chartAt E p).symm y))
      (coordinateVector p y i) =
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i) := by
  rw [metricGradient_pairing]
  have hc : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) (IsManifold.chart_mem_maximalAtlas p) hy).mdifferentiableAt (by simp)
  have hh := mfderiv_comp y (hu.mdifferentiable (by simp) _) hc
  rw [mfderiv_eq_fderiv] at hh
  rw [hh]
  rfl

lemma metricGradient_coordinates (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) (y : E)
    (hy : y ∈ (chartAt E p).target) :
    (metricCoefficients g p y)⁻¹ *ᵥ
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) =
      (chartTangentBasis p y hy).equivFun
        (show E from metricGradient g u ((chartAt E p).symm y)) := by
  let b := chartTangentBasis p y hy
  let v : E := metricGradient g u ((chartAt E p).symm y)
  have he : (metricCoefficients g p y) *ᵥ (b.equivFun v) =
      (fun j => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) := by
    ext i
    rw [← metricGradient_coordinate_pairing g hu p y hy i]
    change (∑ j, g.inner ((chartAt E p).symm y) (b i) (b j) * b.equivFun v j) =
      g.inner ((chartAt E p).symm y) v (b i)
    rw [g.symm _ v (b i)]
    conv_rhs => arg 2; rw [← b.sum_repr v]
    have hsum (L : E →L[ℝ] ℝ) :
        (∑ j, L (b j) * b.repr v j) = L (∑ j, b.repr v j • b j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    exact hsum (g.inner ((chartAt E p).symm y) (b i))
  rw [← he,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (metricCoefficients_det_pos g p hy).ne'),Matrix.one_mulVec]


end


section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff Matrix BoundedContinuousFunction
section ExponentialAlgebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma clm_exp_smul_mul (K : E →L[ℝ] E) (s t : ℝ) :
    NormedSpace.exp (s • K) * NormedSpace.exp (t • K) = NormedSpace.exp ((s+t) • K) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ (E →L[ℝ] E)
  rw [add_smul]
  exact (NormedSpace.exp_add_of_commute (by
    show (s • K) * (t • K) = (t • K) * (s • K)
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm])).symm
end ExponentialAlgebra
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma coordinateGradientPair_eq_inner (g : SmoothMetric E M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (x : M) :
    coordinateGradientPair g u v x = g.inner x (metricGradient g u x) (metricGradient g v x) := by
  classical
  let y := chartAt E x x
  have hy : y ∈ (chartAt E x).target := (chartAt E x).map_source (mem_chart_source E x)
  have hp : (chartAt E x).symm y = x := (chartAt E x).left_inv (mem_chart_source E x)
  let b := chartTangentBasis x y hy
  have hc := metricGradient_coordinates g hv x y hy
  rw [hp] at hc
  have hdu (i : CoordIndex E) :
      g.inner x (metricGradient g u x) (b i) =
      fderiv ℝ (u ∘ (chartAt E x).symm) y (Module.finBasis ℝ E i) := by
    have hh := metricGradient_coordinate_pairing g hu x y hy i
    rw [hp] at hh
    exact hh
  calc
    coordinateGradientPair g u v x = ∑ i, (fderiv ℝ (u ∘ (chartAt E x).symm) y
        (Module.finBasis ℝ E i)) * (((metricCoefficients g x y)⁻¹) *ᵥ
        (fun j => fderiv ℝ (v ∘ (chartAt E x).symm) y (Module.finBasis ℝ E j))) i := by
      simp only [coordinateGradientPair,Matrix.mulVec,dotProduct,Finset.mul_sum,y]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    _ = ∑ i, b.equivFun (show E from metricGradient g v x) i *
        g.inner x (metricGradient g u x) (b i) := by
      rw [hc]
      apply Finset.sum_congr rfl; intro i _
      rw [hdu]; ring
    _ = g.inner x (metricGradient g u x) (metricGradient g v x) := by
      let L : E →L[ℝ] ℝ := g.inner x (metricGradient g u x)
      have hh := congrArg L (b.sum_repr (show E from metricGradient g v x))
      change (∑ i, b.repr (show E from metricGradient g v x) i * L (b i)) = L (show E from metricGradient g v x)
      simpa only [map_sum,map_smul,smul_eq_mul] using hh

lemma pinnedMetric_gradient_general (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    (u : M → ℝ) (t : ℝ) (x : M) :
    metricGradient (pinnedMetric g K hK t) u x =
      (NormedSpace.exp (t • (show E →L[ℝ] E from K x))) (metricGradient g u x) := by
  symm
  apply metricGradient_unique
  intro w
  erw [pinnedMetric_inner]
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner x
  let A : E →L[ℝ] E := K x
  let V : E := metricGradient g u x
  let W : E := w
  have hs : ∀ a b : E, G (((-t/2) • A) a) b = G a (((-t/2) • A) b) := by
    intro a b
    change g.inner x (((-t/2) • (K x : E →L[ℝ] E)) a) b =
      g.inner x a (((-t/2) • (K x : E →L[ℝ] E)) b)
    erw [smul_apply, smul_apply, map_smul, smul_apply, map_smul]
    exact congrArg (fun r : ℝ => (-t/2) • r) (hsa x a b)
  refine Eq.trans ?_ (metricGradient_pairing g u x w)
  change G ((NormedSpace.exp ((-t/2) • A)) ((NormedSpace.exp (t • A)) V))
    ((NormedSpace.exp ((-t/2) • A)) W) = G V W
  calc
    _ = G (((NormedSpace.exp ((-t/2) • A) * NormedSpace.exp ((-t/2) • A)) *
        NormedSpace.exp (t • A)) V) W := by
      exact (clm_exp_selfAdjoint G ((-t/2) • A) hs
        ((NormedSpace.exp ((-t/2) • A)) ((NormedSpace.exp (t • A)) V)) W).symm
    _ = G V W := by
      rw [clm_exp_smul_mul,clm_exp_smul_mul]
      have he : -t/2 + -t/2 + t = 0 := by ring
      rw [he,zero_smul,NormedSpace.exp_zero,one_apply_eq_self]

lemma pinnedMetric_gradientPair (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (t : ℝ) (x : M) :
    coordinateGradientPair (pinnedMetric g K hK t) u v x =
      g.inner x (metricGradient g u x)
        ((NormedSpace.exp (t • (show E →L[ℝ] E from K x))) (metricGradient g v x)) := by
  rw [coordinateGradientPair_eq_inner _ hu hv,metricGradient_pairing,
    pinnedMetric_gradient_general g K hK hsa]
  exact (metricGradient_pairing g u x _).symm

lemma pinnedMetric_gradientPair_deriv (g : SmoothMetric E M)
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (x : M) :
    HasDerivAt (fun t => coordinateGradientPair (pinnedMetric g K hK t) u v x)
      (g.inner x (metricGradient g u x) (K x (metricGradient g v x))) 0 := by
  simp_rw [pinnedMetric_gradientPair g K hK hsa hu hv]
  let L : E →L[ℝ] ℝ := g.inner x (metricGradient g u x)
  exact L.hasFDerivAt.comp_hasDerivAt 0
    (exp_smul_apply_deriv_zero (show E →L[ℝ] E from K x) (show E from metricGradient g v x))
end


open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff Matrix BoundedContinuousFunction
section PinnedJointEnergy
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (g : SmoothMetric E M)
variable (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
variable (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
  (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
variable (hsa : ∀ x v w, g.inner x (K x v) w = g.inner x v (K x w))
variable {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
  (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v)
include hsa hu hv
lemma pinnedMetric_joint_gradientPair (t : ℝ) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => coordinateGradientPair (pinnedMetric g K hK z.1)
      u v ((chartAt E p).symm z.2)) (t,y) := by
  simp_rw [pinnedMetric_gradientPair g K hK hsa hu hv]
  have hf : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞
      (fun z : ℝ × E => (chartAt E p).symm z.2) (t,y) :=
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy).comp (t,y)
      contDiffAt_snd.contMDiffAt
  have hk := (hK _).comp (t,y) hf
  have he := contMDiffAt_exp_along _ (contMDiffAt_smul_along _ hk
    (show ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,ℝ) ∞ (fun z : ℝ × E => z.1) (t,y) from
      contDiffAt_fst.contMDiffAt))
  have hu' := (contMDiff_metricGradient g hu _).comp (t,y) hf
  have hv' := (contMDiff_metricGradient g hv _).comp (t,y) hf
  have hh := ((g.contMDiff _).comp (t,y) hf).clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ)
    hu' (he.clm_bundle_apply hv')
  rw [contMDiffAt_totalSpace] at hh
  exact contMDiffAt_iff_contDiffAt.mp hh.2

lemma continuous_pinned_gradientPair :
    Continuous (fun z : ℝ × M => coordinateGradientPair (pinnedMetric g K hK z.1) u v z.2) := by
  apply continuous_joint_of_chart (E := E) (fun t x => coordinateGradientPair (pinnedMetric g K hK t) u v x)
  intro t p
  exact (pinnedMetric_joint_gradientPair g K hK hsa hu hv t p
    ((chartAt E p).map_source (mem_chart_source E p))).continuousAt

lemma continuous_pinned_gradientPair_time_deriv :
    Continuous (fun z : ℝ × M => deriv
      (fun t => coordinateGradientPair (pinnedMetric g K hK t) u v z.2) z.1) := by
  apply continuous_joint_of_chart (E := E) (fun t x => deriv
    (fun r => coordinateGradientPair (pinnedMetric g K hK r) u v x) t)
  intro t p
  exact (contDiffAt_partial_time_deriv (pinnedMetric_joint_gradientPair g K hK hsa hu hv t p
    ((chartAt E p).map_source (mem_chart_source E p)))).continuousAt

lemma hasDerivAt_pinned_gradientPair_time (t : ℝ) (p : M) :
    HasDerivAt (fun r => coordinateGradientPair (pinnedMetric g K hK r) u v p)
      (deriv (fun r => coordinateGradientPair (pinnedMetric g K hK r) u v p) t) t := by
  have hh := (pinnedMetric_joint_gradientPair g K hK hsa hu hv t p
    ((chartAt E p).map_source (mem_chart_source E p))).comp t
    (show ContDiffAt ℝ ∞ (fun r : ℝ => (r,chartAt E p p)) t from contDiffAt_id.prodMk contDiffAt_const)
  have hf : ContDiffAt ℝ ∞ (fun r => coordinateGradientPair (pinnedMetric g K hK r) u v p) t := by
    simpa only [Function.comp_def,(chartAt E p).left_inv (mem_chart_source E p)] using hh
  exact (hf.differentiableAt (by simp)).hasDerivAt
end PinnedJointEnergy

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

lemma hasDerivAt_mean_family (f d : ℝ → M → ℝ)
    (hc : Continuous (fun z : ℝ × M => f z.1 z.2))
    (hd : Continuous (fun z : ℝ × M => d z.1 z.2))
    (hf : ∀ t x, HasDerivAt (fun r => f r x) (d t x) t) :
    HasDerivAt (fun t => I.mean g (f t)) (I.mean g (d 0)) 0 := by
  let F (t : ℝ) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨f t,hc.comp (continuous_const.prodMk continuous_id)⟩
  let D (t : ℝ) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨d t,hd.comp (continuous_const.prodMk continuous_id)⟩
  have hFD : HasDerivAt F (D 0) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    simpa only [zero_add] using bounded_difference_quotient F D hd hf
  exact (I.integralCLM g).hasFDerivAt.comp_hasDerivAt 0 hFD

omit [CompactSpace M] [T2Space M] in
lemma mean_pinnedMetric (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    (t : ℝ) (f : M → ℝ) : I.mean (pinnedMetric g K hK t) f = I.mean g f := by
  unfold mean
  apply Finset.sum_congr rfl
  intro i _
  unfold metricChartIntegral
  apply setIntegral_congr_fun (chartAt E (i:M)).open_target.measurableSet
  intro y hy
  dsimp only
  rw [pinnedMetric_det g K hK htr t (i:M) y hy]

theorem pinned_laplacian_first_variation
    (K : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x)
    (hK : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E) x (K x)))
    (hsa : ∀ x a b, g.inner x (K x a) b = g.inner x a (K x b))
    (htr : ∀ x, LinearMap.trace ℝ E (show E →L[ℝ] E from K x).toLinearMap = 0)
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) :
    I.mean g (fun x => u x * deriv (fun t => laplaceBeltrami (pinnedMetric g K hK t) v x) 0) =
      -I.mean g (fun x => g.inner x (metricGradient g u x) (K x (metricGradient g v x))) := by
  let q := pinnedMetric g K hK
  have hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
      ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y) := by
    intro p t y hy i j
    exact pinnedMetric_joint_coefficients g K hK p i j t hy
  have hL := I.hasDerivAt_mean_family g
    (fun t x => u x*laplaceBeltrami (q t) v x)
    (fun t x => u x*deriv (fun t => laplaceBeltrami (q t) v x) t)
    ((hu.continuous.comp continuous_snd).mul (continuous_joint_laplaceBeltrami q hq hv))
    ((hu.continuous.comp continuous_snd).mul (continuous_joint_laplaceBeltrami_time_deriv q hq hv))
    (fun t x => by simpa only [zero_mul,zero_add,Pi.mul_apply] using!
      (hasDerivAt_const t (u x)).mul (hasDerivAt_laplaceBeltrami_time q hq hv t x))
  have hE := I.hasDerivAt_mean_family g
    (fun t x => coordinateGradientPair (q t) u v x)
    (fun t x => deriv (fun t => coordinateGradientPair (q t) u v x) t)
    (continuous_pinned_gradientPair g K hK hsa hu hv)
    (continuous_pinned_gradientPair_time_deriv g K hK hsa hu hv)
    (hasDerivAt_pinned_gradientPair_time g K hK hsa hu hv)
  have he : (fun t => I.mean g (fun x => u x*laplaceBeltrami (q t) v x)) =
      fun t => -(I.mean g (coordinateGradientPair (q t) u v)) := by
    funext t
    rw [← I.mean_pinnedMetric g K hK htr t, I.green _ hu hv,I.mean_pinnedMetric g K hK htr t]
  rw [he] at hL
  have hdE : (fun x => deriv (fun t => coordinateGradientPair (q t) u v x) 0) =
      fun x => g.inner x (metricGradient g u x) (K x (metricGradient g v x)) := by
    funext x
    exact (pinnedMetric_gradientPair_deriv g K hK hsa hu hv x).deriv
  rw [hdE] at hE
  exact hL.unique hE.neg
end MetricIntegralAtlas

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_VaryingSpectralResolventBase
attribute [-instance] _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)

lemma scalarTestCLM_pinned_deriv_oai (I : MetricIntegralAtlas (E := E) (M := M))
    {u : M → ℝ} {U : Set M} (K : pinningTensorSpace g u U)
    {a : M → ℝ} (ha : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ a)
    (s : ℝ) (z : A.realH s) (hz : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (A.realValue s z)) :
    A.scalarTestCLM I s (laplaceDerivativeBCF (pinnedMetric g K.val K.property.1)
      (fun p t _ hy i j => pinnedMetric_joint_coefficients g K.val K.property.1 p i j t hy) ha 0) z =
      -I.mean g (fun x => g.inner x (metricGradient g (A.realValue s z) x)
        (K.val x (metricGradient g a x))) := by
  have hh := I.pinned_laplacian_first_variation g K.val K.property.1 K.property.2.1
    K.property.2.2.1 hz ha
  change I.mean g (fun x => deriv (fun t => laplaceBeltrami (pinnedMetric g K.val K.property.1 t) a x) 0*
    A.realValue s z x) = _
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  funext x
  exact mul_comm _ _

end CompactMetricAtlas

end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM_pinned_deriv_oai.{u_1, u_2} := @OAI.YauCounterexamples.CompactMetricAtlas.scalarTestCLM_pinned_deriv_oai.{u_1, u_2}
