-- Prove2me | solution 1 for OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:30:08.369887+00:00
-- url     : https://prove2.me/submissions/3ace7ea8-2562-4d54-baec-51eba7ea4cbb

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A027
import Definitions.Def_OAIQ232A028
import Theorems.Thm_OAI_WeakMTWTransport_WeakMTW_exists_local_outer_chart_jet_bound

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_SmoothSupportSemibound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma bilinear_diag_sub_bound (B C : E →L[ℝ] E →L[ℝ] ℝ) (d:E) :
    |B d d-C d d|≤‖B-C‖*‖d‖^2 := by
  have H := (B-C).le_opNorm₂ d d
  simpa only [sub_apply,Real.norm_eq_abs,pow_two,mul_assoc] using H
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialNull
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder

section TransportCertificates
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

omit [MetricSpace M] [BorelSpace M] in
lemma density_nonnegative {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    ∀ᵐ x ∂vol, 0 ≤ rho x := by
  filter_upwards [hrho.2.2.2] with x hx
  exact hlam.le.trans hx.1

omit [MetricSpace M] [BorelSpace M] in
lemma densityMeasure_probability {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    IsProbabilityMeasure (densityMeasure vol rho) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hrho.2.1 (density_nonnegative hlam hrho),
    hrho.2.2.1, ENNReal.ofReal_one]

end TransportCertificates

open scoped BoundedContinuousFunction

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_CompactDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma cTransform_add_const {v : M → ℝ} (hv : Continuous v) (a : ℝ) :
    cTransform (fun x => v x + a) = fun x => cTransform v x - a := by
  funext x
  apply le_antisymm
  · rw [cTransform_le_iff (v := fun x => v x + a) (hv.add continuous_const)]
    intro y
    have hh := ((cTransform_le_iff hv x (cTransform v x)).mp le_rfl) y
    linarith
  · obtain ⟨y, hy, _⟩ := exists_cTransform_contact hv x
    have hh := cTransform_gap_nonneg (v := fun x => v x + a) (hv.add continuous_const) x y
    dsimp [contactGap] at hh
    linarith

variable [MeasurableSpace M] [BorelSpace M]

omit [CompactSpace M] [Nonempty M] in
lemma dualObjective_add_constants (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (a b : M →ᵇ ℝ) (k : ℝ) :
    dualObjective mu nu (a + BoundedContinuousFunction.const M (-k),
      b + BoundedContinuousFunction.const M k) = dualObjective mu nu (a,b) := by
  change (∫ x, (a x + -k) ∂mu) + (∫ y, (b y + k) ∂nu) = _
  rw [integral_add (a.integrable mu) (integrable_const _),
    integral_add (b.integrable nu) (integrable_const _)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  dsimp [dualObjective]
  ring

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_PoleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma coordinateBackward_contMDiffAt {a : M} {q : ℝ × Model n × (Model n →L[ℝ] ℝ)}
    (hq : q.2.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,ℝ × Model n × (Model n →L[ℝ] ℝ)) 𝓘(ℝ,Model n) ∞
      (coordinateBackward a) q := by
  have hg := (contDiffOn_riemannianCoordinateMetric (E := Model n) a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds hq)
  have hi := (riemannianCoordinateMetric_isInvertible hq).contDiffAt_map_inverse.comp q.2.1 hg
  have hz : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.1) q :=
    contDiffAt_fst.comp q contDiffAt_snd
  have hl : ContDiffAt ℝ ∞ (fun q : ℝ × Model n × (Model n →L[ℝ] ℝ) => q.2.2) q :=
    contDiffAt_snd.comp q contDiffAt_snd
  have hv := (contDiffAt_fst.neg.smul ((hi.comp q hz).clm_apply hl))
  exact (movingNormal_contMDiffAt hq).comp q (hz.prodMk hv).contMDiffAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartGradientMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma chartGradientVector_total_eq {a : M} {q : Model n×(Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm q.1,chartGradientVector a q.1 q.2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) =
      (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).symm
        (q.1,(riemannianCoordinateMetric a q.1).inverse q.2) := by
  have hx : (extChartAt 𝓘(ℝ,Model n) a).symm q.1∈(chartAt (Model n) a).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hq
  dsimp only [chartGradientVector]
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateTrueLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section CoordinateTrueLog
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_chart_covector_for_log {a : M} {p : TangentSpace 𝓘(ℝ,Model n) a}
    (hp : p∈injectivityDomain a) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    ∃ L : Model n →L[ℝ] ℝ,
      chartGradientVector a z L∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      coordinateBackward a (-1,z,L)=riemannianExp a p ∧
      HasFDerivAt (chartCost a (riemannianExp a p)) (-L) z := by
  let : Nonempty M := ⟨a⟩
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let A : TangentBundle 𝓘(ℝ,Model n) M := ⟨a,0⟩
  let P : TangentBundle 𝓘(ℝ,Model n) M := ⟨a,p⟩
  let c := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) A
  let L := riemannianCoordinateMetric a z (c P).2
  have hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hPs : P∈c.source := (tangent_chart_source_iff A P).mpr (mem_extChartAt_source a)
  have he : (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z L⟩ :
      TangentBundle 𝓘(ℝ,Model n) M)=P := by
    rw [chartGradientVector_total_eq (q := (z,L)) hz]
    have hinv : (riemannianCoordinateMetric a z).inverse L=(c P).2 :=
      (riemannianCoordinateMetric_isInvertible hz).inverse_apply_self _
    rw [hinv]
    exact c.left_inv hPs
  have hreg : chartGradientVector a z L∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
    have H : P∈{Q : TangentBundle 𝓘(ℝ,Model n) M | Q.2∈injectivityDomain Q.1} := hp
    rwa [←he] at H
  have hex : coordinateBackward a (-1,z,L)=riemannianExp a p := by
    rw [coordinateBackward_eq_exp_chartGradient hz]
    exact congrArg (fun Q : TangentBundle 𝓘(ℝ,Model n) M => riemannianExp Q.1 Q.2) he
  refine ⟨L,hreg,hex,?_⟩
  rw [←hex]
  exact chartCost_gradient_at_contact hz hreg

end CoordinateTrueLog
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactCrossing
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bilinear_lower_of_unit (L : E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ}
    (h : ∀ v:E, ‖v‖=1 → c ≤ L v v) (v:E) : c*‖v‖^2 ≤ L v v := by
  by_cases hv : v=0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖=1 := by simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have he : v=‖v‖ • w := by dsimp [w]; rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  have H := mul_le_mul_of_nonneg_left (h w hw) (sq_nonneg ‖v‖)
  calc
    c*‖v‖^2 = ‖v‖^2*c := mul_comm _ _
    _ ≤ ‖v‖^2*L w w := H
    _ = L (‖v‖ • w) (‖v‖ • w) := by simp only [map_smul,smul_apply,smul_eq_mul] <;> ring
    _ = L v v := by rw [←he]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveBilinearBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Metric

namespace WeakMTWTransport
section PositiveBilinearBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_bilinear_positive_baseline (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) :
    ∃ m>0,∀ v : E,m*‖v‖^2≤B v v := by
  let S := sphere (0:E) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hc : ContinuousOn (fun v:E => B v v) S :=
    (B.continuous.clm_apply continuous_id).continuousOn
  obtain ⟨m,hm,Hm⟩ : ∃ m>0,∀ v∈S,m≤B v v := by
    by_cases hne : S.Nonempty
    · obtain ⟨v,hv,Hv⟩ := hS.exists_isMinOn hne hc
      have hn : ‖v‖=1 := by simpa only [S,mem_sphere,dist_zero_right] using hv
      have hp : 0 < B v v := hB v (by intro he; simp [he] at hn)
      exact ⟨B v v,hp,fun w hw => Hv hw⟩
    · exact ⟨1,zero_lt_one,fun v hv => (hne ⟨v,hv⟩).elim⟩
  exact ⟨m,hm,bilinear_lower_of_unit B (fun v hv => Hm v (by simpa only [S,mem_sphere,dist_zero_right] using hv))⟩

end PositiveBilinearBound
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section DividedBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma divided_hessian_decrease {a : M} {r ξ : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hs : s<1) :
    hessianValue a (s • r) ξ/s ≤ hessianValue a (t • r) ξ/t := by
  rcases eq_or_lt_of_le hts with h | h
  · simp only [h,le_refl]
  by_cases hξ : ξ=0
  · subst ξ
    rw [hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr (ht.trans h) hs),
      hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr ht (h.trans hs))]
    simp only [map_zero,zero_div,le_refl]
  exact (divided_hessian_strict_decrease hr ht h hs hξ).le

lemma exists_divided_hessian_baseline {a : M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s0 : ℝ} (ht : 0 < t) (hts : t < s0) (hs0 : s0<1) :
    ∃ m>0,∀ s : ℝ,s0 ≤ s → s<1 → ∀ ξ : TangentSpace 𝓘(ℝ,Model n) a,
      m*‖ξ‖^2 ≤ hessianValue a (t • r) ξ/t-hessianValue a (s • r) ξ/s := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) a) := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let B := t⁻¹ • normalHessian a (t • r)-s0⁻¹ • normalHessian a (s0 • r)
  have hIDt := contracted_minimizer_mem_injectivityDomain hr ht (hts.trans hs0)
  have hIDs := contracted_minimizer_mem_injectivityDomain hr (ht.trans hts) hs0
  have hB (ξ : TangentSpace 𝓘(ℝ,Model n) a) : B ξ ξ=
      hessianValue a (t • r) ξ/t-hessianValue a (s0 • r) ξ/s0 := by
    rw [hessianValue_eq_normalHessian hIDt,hessianValue_eq_normalHessian hIDs]
    simp only [B,sub_apply,smul_apply,smul_eq_mul]
    ring
  obtain ⟨m,hm,Hm⟩ := exists_bilinear_positive_baseline B (fun ξ hξ => by
    rw [hB]
    exact sub_pos.mpr (divided_hessian_strict_decrease hr ht hts hs0 hξ))
  refine ⟨m,hm,?_⟩
  intro s hss hs1 ξ
  have H := Hm ξ
  rw [hB] at H
  have Hd := divided_hessian_decrease (ξ := ξ) hr (ht.trans hts) hss hs1
  linarith only [H,Hd]

end DividedBaseline
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BranchDividedBaseline
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section BranchDividedBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma cost_branch_hessian_inward_limit {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    (ξ : TangentSpace 𝓘(ℝ,Model n) a) :
    Tendsto (fun s:ℝ => hessianValue a (s • r) ξ/s) (𝓝[<] 1)
      (𝓝 (fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a r))) 0 ξ ξ)) := by
  have H := cost_branch_normal_jets (r := r) (T := (1:ℝ)) (by norm_num)
    (by simpa only [one_smul] using hG) (by simpa only [one_smul] using hagree)
    (fun s hs => contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
  have HH := (H.2.2 ξ).div (tendsto_id.mono_left nhdsWithin_le_nhds) (by norm_num : (1:ℝ)≠0)
  change Tendsto (fun s:ℝ => hessianValue a (s • r) ξ/s) (𝓝[<] 1)
    (𝓝 ((fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a ((1:ℝ) • r))))) 0 ξ ξ / 1)) at HH
  simpa only [one_smul,div_one] using HH

lemma exists_branch_divided_baseline {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t:ℝ} (ht : 0 < t) (ht1 : t < 1)
    {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∃ m>0,∀ ξ:TangentSpace 𝓘(ℝ,Model n) a,
      m*‖ξ‖^2 ≤ hessianValue a (t • r) ξ/t-
        fderiv ℝ (fderiv ℝ (fun w => G (riemannianExp a w,riemannianExp a r))) 0 ξ ξ := by
  let s0 := (t+1)/2
  have hts : t < s0 := by dsimp [s0] <;> linarith
  have hs0 : s0 < 1 := by dsimp [s0] <;> linarith
  obtain ⟨m,hm,Hm⟩ := exists_divided_hessian_baseline hr ht hts hs0
  refine ⟨m,hm,?_⟩
  intro ξ
  have H := ((tendsto_const_nhds (x := hessianValue a (t • r) ξ/t)).sub (cost_branch_hessian_inward_limit hr hG hagree ξ))
  apply ge_of_tendsto H
  filter_upwards [(eventually_gt_nhds hs0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hs1
  exact Hm s hs.le hs1 ξ

end BranchDividedBaseline
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiberLog
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_fiber_log {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ L : M → TangentSpace 𝓘(ℝ,Model n) x,
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ L
        (riemannianExp x p) ∧
      L (riemannianExp x p)=p ∧
      (∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (L y)=y) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hpe,hei⟩ := exists_coordinate_exp_inverse hp
  have hep : e p=d y := by rw [he]
  let L : M → V := fun z => e.symm (d z)
  have hL : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L y :=
    (show ContDiffAt ℝ ∞ e.symm (d y) from hep ▸ hei).contMDiffAt.comp y
      (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from contMDiffAt_extChartAt)
  have hLy : L y=p := by dsimp [L]; rw [←hep,e.left_inv hpe]
  refine ⟨L,hL,hLy,?_⟩
  have ht : ∀ᶠ z in 𝓝 y, d z∈e.target :=
    (continuousAt_extChartAt y).eventually
      ((e.open_target.mem_nhds (hep ▸ e.map_source hpe)))
  have hcont : ContinuousAt (fun z => riemannianExp x (L z)) y :=
    (continuous_riemannianExp x).continuousAt.comp hL.continuousAt
  have hs : ∀ᶠ z in 𝓝 y, riemannianExp x (L z)∈d.source := by
    have H := hcont.eventually (show d.source∈𝓝 (riemannianExp x (L y)) from by
      rw [hLy]; exact extChartAt_source_mem_nhds y)
    exact H
  filter_upwards [ht,hs,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y] with z hzt hzs hsz
  apply d.injOn hzs hsz
  have HR := e.right_inv hzt
  rw [he] at HR
  exact HR

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_chart_fiber_log {x a : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x)
    (ha : riemannianExp x p∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    let ψ := extChartAt 𝓘(ℝ,Model n) a
    let u := ψ (riemannianExp x p)
    ∃ e : Model n → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ e u ∧ e u=p ∧
      (∀ᶠ w in 𝓝 u, riemannianExp x (e w)=ψ.symm w) ∧
      Function.Injective (fderiv ℝ e u) := by
  let ψ := extChartAt 𝓘(ℝ,Model n) a
  let u := ψ (riemannianExp x p)
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hu : u∈ψ.target := ψ.map_source ha
  have hui : ψ.symm u=riemannianExp x p := ψ.left_inv ha
  obtain ⟨L,hL,hLp,hLi⟩ := exists_smooth_fiber_log hp
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ ψ.symm u :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hu)
  let e := fun w : Model n => L (ψ.symm w)
  have he : ContDiffAt ℝ ∞ e u :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L (ψ.symm u) from by
      simpa only [hui] using hL).comp u hi).contDiffAt
  have heu : e u=p := by dsimp [e]; rw [hui]; exact hLp
  have hei : ∀ᶠ w in 𝓝 u, riemannianExp x (e w)=ψ.symm w :=
    hi.continuousAt.eventually (by simpa only [hui] using hLi)
  refine ⟨e,he,heu,hei,?_⟩
  let c : V → Model n := fun v => ψ (riemannianExp x v)
  have hc : ContDiffAt ℝ ∞ c p :=
    ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n)) (by
      simpa only [extChartAt_source] using ha)).comp p
        (contMDiff_riemannianExp_fiber x p)).contDiffAt
  have hid : (fun w => c (e w)) =ᶠ[𝓝 u] (fun w => w) := by
    filter_upwards [hei,(isOpen_extChartAt_target a).mem_nhds hu] with w hw hwt
    dsimp [c]
    rw [hw,ψ.right_inv hwt]
  have HD := hid.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp u (by simpa only [heu] using hc.differentiableAt (by simp))
    (he.differentiableAt (by simp)),fderiv_fun_id] at HD
  intro v w hvw
  change fderiv ℝ e u v=fderiv ℝ e u w at hvw
  have H := congrArg (fun C : Model n →L[ℝ] Model n => C v-C w) HD
  apply sub_eq_zero.mp
  simpa only [ContinuousLinearMap.comp_apply,hvw,sub_self,ContinuousLinearMap.id_apply] using H.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_StationaryPullback
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_sub {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f a-g a)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w-fderiv ℝ (fderiv ℝ g) x v w := by
  have he : fderiv ℝ (fun a => f a-g a) =ᶠ[𝓝 x]
      (fun a => fderiv ℝ f a-fderiv ℝ g a) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with a ha hb
    exact fderiv_fun_sub (ha.differentiableAt (by norm_num)) (hb.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  rw [fderiv_fun_sub ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  rfl

lemma second_fderiv_const_mul {f : E → ℝ} {x : E} (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => c*f a)) x v w = c*fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fderiv ℝ (c • f)) x v w = _
  rw [fderiv_const_smul_field c]
  rw [fderiv_const_smul_field (f := fderiv ℝ f) c]
  rfl

lemma second_fderiv_comp_stationary {f : F → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x)
    (hzero : fderiv ℝ f (g x)=0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually (hf.eventually (by norm_num)),
      hg.eventually (by norm_num)] with a hfa hga
    exact ((hfa.differentiableAt (by norm_num)).hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,hzero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_comp,zero_apply,
    zero_add,add_zero,add_apply] using H

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_NormLower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]

lemma exists_norm_sq_lower_of_injective (L : E →L[ℝ] F) (hL : Function.Injective L) :
    ∃ c>0, ∀ v:E, c*‖v‖^2 ≤ ‖L v‖^2 := by
  obtain ⟨K,hK,HK⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hL
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  refine ⟨((K:ℝ)^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hKr),?_⟩
  intro v
  have H := ZeroHomClass.bound_of_antilipschitz L HK v
  have H2 := (sq_le_sq₀ (norm_nonneg v) (mul_nonneg K.coe_nonneg (norm_nonneg (L v)))).mpr H
  rw [mul_pow] at H2
  have HH : ‖v‖^2/(K:ℝ)^2 ≤ ‖L v‖^2 :=
    (div_le_iff₀ (sq_pos_of_pos hKr)).mpr (by simpa only [mul_comm] using H2)
  simpa only [div_eq_mul_inv,mul_comm] using HH

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_BranchChartBaseline
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section BranchChartBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma exists_branch_chart_baseline {a:M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    {l:ℝ} (hl : 1<l) :
    let z := extChartAt 𝓘(ℝ,Model n) a a
    let c := fun w:Model n => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,riemannianExp a r)
    ContDiffAt ℝ 2 c z ∧
    ∃ L:Model n →L[ℝ] ℝ, fderiv ℝ c z= -l • L ∧
      chartGradientVector a z L∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm z) ∧
      ∃ m>0,∀ d:Model n,m*‖d‖^2≤
        l*fderiv ℝ (fderiv ℝ (chartCost a (coordinateBackward a (-1,z,L)))) z d d-
        fderiv ℝ (fderiv ℝ c) z d d := by
  dsimp only
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let V := TangentSpace 𝓘(ℝ,Model n) a
  let c := fun w:Model n => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,riemannianExp a r)
  let b := riemannianExp a (l⁻¹ • r)
  let cN : V → ℝ := fun v => G (riemannianExp a v,riemannianExp a r)
  let cT := normalCost a (l⁻¹ • r)
  have hlp : 0<l := zero_lt_one.trans hl
  have ht : 0<l⁻¹ := inv_pos.mpr hlp
  have ht1 : l⁻¹<1 := (inv_lt_one₀ hlp).mpr hl
  have hp := contracted_minimizer_mem_injectivityDomain hr ht ht1
  obtain ⟨m,hm,Hm⟩ := exists_branch_divided_baseline hr ht ht1 hG hagree
  have hCJ := cost_branch_normal_jets (r := r) (T := (1:ℝ)) (by norm_num)
    (by simpa only [one_smul] using hG) (by simpa only [one_smul] using hagree)
    (fun s hs => contracted_minimizer_mem_injectivityDomain hr hs.1 hs.2)
  have hcN : ContDiffAt ℝ 2 cN 0 := by
    have hh : ContDiffAt ℝ ∞ cN 0 := by simpa only [cN,one_smul] using hCJ.1
    exact hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcND : fderiv ℝ cN 0=innerSL ℝ (-r) := by simpa only [cN,one_smul] using hCJ.2.1.fderiv
  have hcT : ContDiffAt ℝ 2 cT 0 :=
    (normalCost_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨L,hLreg,hLb,hLD⟩ := exists_chart_covector_for_log hp
  obtain ⟨e,he,he0,hei,hi⟩ := exists_smooth_chart_fiber_log (a := a)
    (zero_mem_injectivityDomain (n := n) a)
    (by simpa only [riemannianExp_zero] using mem_extChartAt_source (I := 𝓘(ℝ,Model n)) a)
  simp only [riemannianExp_zero] at he he0 hei hi
  change ContDiffAt ℝ ∞ e z at he
  change e z=0 at he0
  change Function.Injective (fderiv ℝ e z) at hi
  have he2 : ContDiffAt ℝ 2 e z := he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨k,hk,Hk⟩ := exists_norm_sq_lower_of_injective (fderiv ℝ e z) hi
  have hce : c =ᶠ[𝓝 z] (fun w => cN (e w)) := by
    filter_upwards [hei] with w hw
    simp only [c,cN,hw]
  have hTe : chartCost a b =ᶠ[𝓝 z] (fun w => cT (e w)) := by
    filter_upwards [hei] with w hw
    simp only [cT,b,normalCost,chartCost,hw]
  have hc : ContDiffAt ℝ 2 c z := ((he0.symm ▸ hcN).comp z he2).congr_of_eventuallyEq hce
  have hT : ContDiffAt ℝ 2 (chartCost a b) z := ((he0.symm ▸ hcT).comp z he2).congr_of_eventuallyEq hTe
  have hstat : fderiv ℝ (fun v => l*cT v-cN v) 0=0 := by
    rw [fderiv_fun_sub ((hcT.differentiableAt (by norm_num)).const_mul _) (hcN.differentiableAt (by norm_num))]
    change fderiv ℝ (l • cT) 0-fderiv ℝ cN 0=0
    rw [fderiv_const_smul_field,Pi.smul_apply,hcND,(normalCost_hasFDerivAt_zero hp).fderiv]
    simp only [map_neg,map_smul,smul_neg,smul_smul,mul_inv_cancel₀ hlp.ne',one_smul,sub_self]
  have hstatC : fderiv ℝ (fun w => l*chartCost a b w-c w) z=0 := by
    have H : (fun w => l*chartCost a b w-c w)=ᶠ[𝓝 z] (fun w => l*cT (e w)-cN (e w)) := by
      filter_upwards [hTe,hce] with w hw hw'
      rw [hw,hw']
    rw [H.fderiv_eq,fderiv_fun_comp z (g := fun v:V => l*cT v-cN v)
      (by simpa only [he0] using (((contDiffAt_const (c := l)).mul hcT).sub hcN).differentiableAt (by norm_num))
      (he2.differentiableAt (by norm_num)),he0,hstat,ContinuousLinearMap.zero_comp]
  have hcD : fderiv ℝ c z= -l • L := by
    rw [fderiv_fun_sub ((hT.differentiableAt (by norm_num)).const_mul _) (hc.differentiableAt (by norm_num))] at hstatC
    change fderiv ℝ (l • chartCost a b) z-fderiv ℝ c z=0 at hstatC
    rw [fderiv_const_smul_field,Pi.smul_apply,hLD.fderiv] at hstatC
    calc
      _ = l • (-L) := (sub_eq_zero.mp hstatC).symm
      _ = -l • L := by ext d; simp only [smul_apply,neg_apply,smul_eq_mul,mul_neg,neg_mul]
  refine ⟨hc,L,hcD,hLreg,m*k,mul_pos hm hk,?_⟩
  intro d
  have HF := second_fderiv_comp_stationary (f := fun v => l*cT v-cN v) (g := e)
    (he0.symm ▸ (contDiffAt_const.mul hcT).sub hcN) he2 (by rwa [he0]) d d
  rw [he0,second_fderiv_sub (contDiffAt_const.mul hcT) hcN,second_fderiv_const_mul] at HF
  have H : (fun w => l*chartCost a b w-c w)=ᶠ[𝓝 z] (fun w => l*cT (e w)-cN (e w)) := by
    filter_upwards [hTe,hce] with w hw hw'
    rw [hw,hw']
  have HH := congrArg (fun A:Model n →L[ℝ] Model n →L[ℝ] ℝ => A d d) H.fderiv.fderiv_eq
  rw [second_fderiv_sub (contDiffAt_const.mul hT) hc,second_fderiv_const_mul] at HH
  rw [hLb,HH,HF]
  have Hb := Hm (fderiv ℝ e z d)
  rw [hessianValue_eq_normalHessian hp] at Hb
  change m*‖fderiv ℝ e z d‖^2≤
    fderiv ℝ (fderiv ℝ cT) 0 (fderiv ℝ e z d) (fderiv ℝ e z d)/l⁻¹-
      fderiv ℝ (fderiv ℝ cN) 0 (fderiv ℝ e z d) (fderiv ℝ e z d) at Hb
  rw [div_inv_eq_mul] at Hb
  nlinarith only [Hb,mul_le_mul_of_nonneg_left (Hk d) hm.le]

end BranchChartBaseline
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_BranchChartJets
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner _root_.OAI.WeakMTWTransport.riemannianExp_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section BranchChartJets
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma branch_chart_jet_continuous {G : M×M → ℝ} {a y : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      G ((extChartAt 𝓘(ℝ,Model n) a).symm z,y)) :
    ContinuousAt (fun q : Model n×M => fderiv ℝ (fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)) q.1) (z,y) ∧
    ContinuousAt (fun q : Model n×M => fderiv ℝ (fderiv ℝ ((fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)))) q.1) (z,y) ∧
    ∀ᶠ q : Model n×M in 𝓝 (z,y), ContDiffAt ℝ 2 ((fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2))) q.1 := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let d := extChartAt 𝓘(ℝ,Model n) y
  let F : Model n → Model n → ℝ := fun b z => G (χ.symm z,d.symm b)
  have hdy : d.symm (d y)=y := d.left_inv (mem_extChartAt_source y)
  have hA : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×Model n => χ.symm q.2) (d y,z) :=
    ((contMDiffWithinAt_extChartAt_symm_target a hz).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds hz)).comp (d y,z) contDiffAt_snd.contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : Model n×Model n => d.symm q.1) (d y,z) :=
    ((contMDiffWithinAt_extChartAt_symm_target y
      (d.map_source (mem_extChartAt_source y))).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (d.map_source (mem_extChartAt_source y)))).comp
      (d y,z) contDiffAt_fst.contMDiffAt
  have hF : ContDiffAt ℝ ∞ (Function.uncurry F) (d y,z) := by
    have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      G (χ.symm z,d.symm (d y)) := by simpa only [hdy] using hc
    exact (hc'.comp (d y,z) (hA.prodMk hB)).contDiffAt
  have hchart : ContinuousAt d y := continuousAt_extChartAt y
  have hq : ContinuousAt (fun q : Model n×M => (d q.2,q.1)) (z,y) :=
    (hchart.comp (x := (z,y)) (f := fun q : Model n×M => q.2) continuousAt_snd).prodMk continuousAt_fst
  have hnear : ∀ᶠ q : Model n×M in 𝓝 (z,y), q.2∈d.source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds y)
  have heq : ∀ᶠ q : Model n×M in 𝓝 (z,y), F (d q.2)=(fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)) := by
    filter_upwards [hnear] with q hq
    funext w
    dsimp [F,χ]
    rw [d.left_inv hq]
  refine ⟨?_,?_,?_⟩
  · have H := (ContDiffAt.partial_snd_fderiv hF).continuousAt.comp
      (x := (z,y)) (f := fun q : Model n×M => (d q.2,q.1)) hq
    apply H.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    change fderiv ℝ (fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)) q.1 =
      fderiv ℝ (F (d q.2)) q.1
    rw [hq]
  · have H := (ContDiffAt.partial_snd_fderiv_two hF).continuousAt.comp
      (x := (z,y)) (f := fun q : Model n×M => (d q.2,q.1)) hq
    apply H.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    change fderiv ℝ (fderiv ℝ ((fun w => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,q.2)))) q.1 =
      fderiv ℝ (fderiv ℝ (F (d q.2))) q.1
    rw [hq]
  · have H := (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    filter_upwards [hq.tendsto.eventually H,heq] with q hq he
    have H' := hq.comp q.1 (contDiffAt_const.prodMk contDiffAt_id)
    change ContDiffAt ℝ 2 (F (d q.2)) q.1 at H'
    rw [he] at H'
    exact H'

end BranchChartJets
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

variable [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma reverseNormalizedPair_mem {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ normalizedDualPairs x0) :
    reverseNormalizedPair x0 uv ∈ normalizedDualPairs x0 := by
  change (uv.2 x0 + -uv.2 x0 = 0) ∧ _ ∧ _
  refine ⟨add_neg_cancel _, ?_, ?_⟩
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.1 y + uv.2 x0) x = uv.2 x + -uv.2 x0
    rw [cTransform_add_const uv.1.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.2
    change cTransform uv.1 x = uv.2 x at hh
    change cTransform uv.1 x - uv.2 x0 = uv.2 x + -uv.2 x0
    rw [hh]
    ring
  · apply BoundedContinuousFunction.ext
    intro x
    change cTransform (fun y => uv.2 y + -uv.2 x0) x = uv.1 x + uv.2 x0
    rw [cTransform_add_const uv.2.continuous]
    have hh := congrArg (fun f : M →ᵇ ℝ => f x) huv.2.1
    change cTransform uv.2 x = uv.1 x at hh
    change cTransform uv.2 x - -uv.2 x0 = uv.1 x + uv.2 x0
    rw [hh]
    ring

lemma densityDualClass_reverse {vol : Measure M} {lam cap : ℝ} (hlam : 0 < lam)
    {x0 : M} {uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)}
    (huv : uv ∈ densityDualClass vol lam cap x0) :
    reverseNormalizedPair x0 uv ∈ densityDualClass vol lam cap x0 := by
  obtain ⟨hnorm, rho0, rho1, hrho0, hrho1, hmin⟩ := huv
  let := densityMeasure_probability hlam hrho0
  let := densityMeasure_probability hlam hrho1
  refine ⟨reverseNormalizedPair_mem hnorm, rho1, rho0, hrho1, hrho0, ?_⟩
  intro a b hab
  have hba : ∀ x y, 0 ≤ contactGap b a x y := by
    intro x y
    have hh := hab y x
    dsimp [contactGap] at hh ⊢
    rw [cost_symm y x] at hh
    linarith
  have hh := hmin b a hba
  rw [reverseNormalizedPair, dualObjective_add_constants]
  dsimp [dualObjective] at hh ⊢
  linarith

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_LocalBranchJetBound
attribute [-simp] _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section LocalBranchJetBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_branch_jet_bound (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0<lam) (hcap : 0 ≤ cap) {a:M}
    {r : TangentSpace 𝓘(ℝ,Model n) a} (hr : r∈minimizingVectors a)
    {G : M×M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (a,riemannianExp a r))
    (hagree : ∀ᶠ z in 𝓝 (⟨a,r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 →
      (fun q:M×M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    {l:ℝ} (hl : 1<l) :
    let c := fun y:M => fun w:Model n => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,y)
    ∃ U : Set ((Model n×M)×ℝ),
      U∈𝓝 ((extChartAt 𝓘(ℝ,Model n) a a,riemannianExp a r),l) ∧ ∃ C≥0,
      ∀ q∈U,∀ (x0:M) (uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀ φ:ℝ → ℝ,StrictMono φ →
      ContDiffAt ℝ 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) →
      HasDerivAt φ q.2 (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) →
      iteratedDeriv 2 φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))≤0 →
      ∀ H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀ d,0≤H d d) →
      HasLowerSecondTaylor (fun h =>
        φ (uv.1 ((extChartAt 𝓘(ℝ,Model n) a).symm (q.1.1+h)))+c q.1.2 (q.1.1+h)) 0 H →
      ∀ d,H d d≤C*‖d‖^2 := by
  dsimp only
  let z := extChartAt 𝓘(ℝ,Model n) a a
  let b := riemannianExp a r
  let q0 : (Model n×M)×ℝ := ((z,b),l)
  let c := fun y:M => fun w:Model n => G ((extChartAt 𝓘(ℝ,Model n) a).symm w,y)
  obtain ⟨hc,L,hcD,hpreg,m,hm,Hm⟩ := exists_branch_chart_baseline hr hG hagree hl
  have hlp : 0<l := zero_lt_one.trans hl
  let δ := m/(4*(l+1))
  have hδ : 0<δ := div_pos hm (by positivity)
  obtain ⟨N,hN,C,hC,HC⟩ := hmtw.exists_local_outer_chart_jet_bound hlam hcap a L hpreg hδ
    (show 0<l+1 by positivity)
  have ha : z∈(extChartAt 𝓘(ℝ,Model n) a).target := mem_extChartAt_target a
  have hGa : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      ((extChartAt 𝓘(ℝ,Model n) a).symm z,b) := by
    simpa only [z,b,(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)] using hG
  obtain ⟨hD,hH,hcnear⟩ := branch_chart_jet_continuous ha hGa
  let P := fun q:(Model n×M)×ℝ => q.2⁻¹ • (-fderiv ℝ (c q.1.2) q.1.1)
  have hP0 : P q0=L := by
    dsimp only [P,q0,c,z,b]
    rw [hcD]
    ext d
    simp only [smul_apply,neg_apply,smul_eq_mul,neg_mul,neg_neg]
    field_simp [hlp.ne']
  have hP : ContinuousAt P q0 :=
    (continuousAt_snd.inv₀ hlp.ne').smul ((hD.comp (x := q0) (f := fun q : (Model n×M)×ℝ => q.1) continuousAt_fst).neg)
  let J := fun q:(Model n×M)×ℝ => (q.1.1,P q)
  have hJ : ContinuousAt J q0 := (continuousAt_fst.comp continuousAt_fst).prodMk hP
  have hJ0 : J q0=(z,L) := by simp only [J,q0,hP0]
  let Y := fun q:(Model n×M)×ℝ => coordinateBackward a (-1,q.1.1,P q)
  have hY : ContinuousAt Y q0 :=
    ((coordinateBackward_contMDiffAt (q := (-1,z,P q0)) ha).continuousAt).comp (x := q0)
      (f := fun q : (Model n×M)×ℝ => (-1,q.1.1,P q)) (continuousAt_const.prodMk hJ)
  have hY0 : Y q0=coordinateBackward a (-1,z,L) := by simp only [Y,q0,hP0]
  have hcost : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q:M×M => cost q.1 q.2) ((extChartAt 𝓘(ℝ,Model n) a).symm z,Y q0) := by
    rw [hY0,coordinateBackward_eq_exp_chartGradient ha]
    exact cost_contMDiffAt_of_injectivityDomain
      (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,chartGradientVector a z L⟩ : TangentBundle 𝓘(ℝ,Model n) M) hpreg
  have htrue := (chartCost_jet_continuous ha hcost).1.comp (x := q0)
    (f := fun q : (Model n×M)×ℝ => (q.1.1,Y q))
    ((continuousAt_fst.comp continuousAt_fst).prodMk hY)
  let W := fun q:(Model n×M)×ℝ =>
    q.2 • fderiv ℝ (fderiv ℝ (chartCost a (Y q))) q.1.1-fderiv ℝ (fderiv ℝ (c q.1.2)) q.1.1
  let : NormedAddCommGroup (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have hW : ContinuousAt W q0 := (continuousAt_snd.smul htrue).sub (hH.comp (x := q0) (f := fun q : (Model n×M)×ℝ => q.1) continuousAt_fst)
  have hW0 (d:Model n) : m*‖d‖^2≤W q0 d d := by
    dsimp only [W,q0]
    rw [hY0]
    exact Hm d
  let U := {q:(Model n×M)×ℝ | J q∈N ∧ 0<q.2 ∧ q.2≤l+1 ∧
    ContDiffAt ℝ 2 (c q.1.2) q.1.1 ∧ ‖W q-W q0‖< m/2}
  have hU : U∈𝓝 q0 := by
    have hn := hJ.preimage_mem_nhds (by rwa [hJ0])
    have hnW : ∀ᶠ q in 𝓝 q0,‖W q-W q0‖< m/2 := by
      filter_upwards [hW.tendsto.eventually
        (Metric.ball_mem_nhds (W q0) (show 0 < m/2 by positivity))] with q hq
      change dist (W q) (W q0) < m/2 at hq
      rwa [dist_eq_norm (W q) (W q0)] at hq
    filter_upwards [hn,continuousAt_snd.preimage_mem_nhds (lt_mem_nhds hlp),
      continuousAt_snd.preimage_mem_nhds (gt_mem_nhds (show l<l+1 by linarith)),
      continuousAt_fst.tendsto.eventually hcnear,hnW] with q hq hp hu hs hw
    exact ⟨hq,hp,hu.le,hs,hw⟩
  refine ⟨U,hU,C,hC,?_⟩
  intro q hq x0 uv huv φ hmono hφ hd hconc H hHjet hjet d
  obtain ⟨hqN,hqpos,hqmax,hqc,hqW⟩ := hq
  have hbase (e:Model n) : 2*δ*q.2*‖e‖^2≤W q e e := by
    have Hb := hW0 e
    have Habs := (abs_le.mp (bilinear_diag_sub_bound (W q) (W q0) e)).1
    have Hsmall := mul_le_mul_of_nonneg_right hqW.le (sq_nonneg ‖e‖)
    have Hl : 2*δ*q.2≤ m/2 := by
      calc
        _ ≤ 2*δ*(l+1) := mul_le_mul_of_nonneg_left hqmax (by positivity)
        _ = m/2 := by dsimp [δ]; field_simp [show l+1≠0 by positivity] <;> ring
    have Hδ := mul_le_mul_of_nonneg_right Hl (sq_nonneg ‖e‖)
    nlinarith only [Hb,Habs,Hsmall,Hδ]
  exact HC x0 uv huv q.1.1 (c q.1.2) q.2 hqpos hqmax hqc hqN hbase
    φ hmono hφ hd hconc H hHjet hjet d

end LocalBranchJetBound
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_BranchJetSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section BranchJetSecond
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.exists_local_branch_jet_bound_second_oai (hmtw:WeakMTW (n := n) (M := M))
    {lam cap:ℝ} (hlam:0 < lam) (hcap:0 ≤ cap) {a:M}
    {r:TangentSpace 𝓘(ℝ,Model n) a} (hr:r∈minimizingVectors a)
    {G:M×M → ℝ}
    (hG:ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G (a,riemannianExp a r))
    (hagree:∀ᶠ z in 𝓝 (⟨a,r⟩:TangentBundle 𝓘(ℝ,Model n) M),
      z.2∈injectivityDomain z.1 → (fun q:M×M=>cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G)
    {l:ℝ} (hl:1 < l) :
    let d:=extChartAt 𝓘(ℝ,Model n) a
    ∃ U:Set ((Model n×M)×ℝ),U∈𝓝 ((d a,riemannianExp a r),l) ∧ ∃ C≥0,
      ∀q∈U,∀(x0:M) (uv:(M →ᵇ ℝ)×(M →ᵇ ℝ)),
      uv∈densityDualClass (metricVolume n) lam cap x0 →
      ∀φ:ℝ → ℝ,StrictMono φ → ContDiffAt ℝ 2 φ (uv.2 (d.symm q.1.1)) →
      HasDerivAt φ q.2 (uv.2 (d.symm q.1.1)) →
      iteratedDeriv 2 φ (uv.2 (d.symm q.1.1)) ≤ 0 →
      ∀H:Model n →L[ℝ] Model n →L[ℝ] ℝ,(∀w,0 ≤ H w w) →
      HasLowerSecondTaylor (fun w=>φ (uv.2 (d.symm (q.1.1+w)))+G (d.symm (q.1.1+w),q.1.2)) 0 H →
      ∀w,H w w ≤ C*‖w‖^2 := by
  dsimp only
  obtain ⟨U,hU,C,hC,HC⟩:=hmtw.exists_local_branch_jet_bound hlam hcap hr hG hagree hl
  refine ⟨U,hU,C,hC,?_⟩
  intro q hq x0 uv huv φ hmono hφ hd hconc H hH hjet w
  let vu:=reverseNormalizedPair x0 uv
  let ψ:=fun s:ℝ=>φ (uv.2 x0+s)
  have heq (y:M):uv.2 x0+vu.1 y=uv.2 y := by
    change uv.2 x0+(uv.2 y+-uv.2 x0)=uv.2 y
    ring
  have hψ:ContDiffAt ℝ 2 ψ (vu.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) :=
    ((heq _).symm ▸ hφ).comp _ (contDiffAt_const.add contDiffAt_id)
  have hdψ:HasDerivAt ψ q.2 (vu.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) := by
    have hd':HasDerivAt φ q.2 (uv.2 x0+vu.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) := (heq _).symm ▸ hd
    have HH:=hd'.comp _ ((hasDerivAt_id _).const_add (uv.2 x0))
    simpa only [mul_one,Function.comp_def,ψ] using HH
  have hcψ:iteratedDeriv 2 ψ (vu.1 ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) ≤ 0 := by
    dsimp only [ψ]
    rw [iteratedDeriv_comp_const_add]
    dsimp only
    rw [heq]
    exact hconc
  apply HC q hq x0 vu (densityDualClass_reverse hlam huv) ψ
    (fun _ _ h=>hmono (by linarith)) hψ hdψ hcψ H hH _ w
  simpa only [ψ,heq] using hjet

end BranchJetSecond
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second_oai.{u_1} := @OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second_oai.{u_1}
