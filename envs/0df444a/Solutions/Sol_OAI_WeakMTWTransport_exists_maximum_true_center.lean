-- Prove2me | solution 1 for OAI.WeakMTWTransport.exists_maximum_true_center
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:43:33.303445+00:00
-- url     : https://prove2.me/submissions/5c68d799-b15e-4e9a-b704-5f0864434638

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
import Definitions.Def_OAIQ232A031
import Theorems.Thm_OAI_WeakMTWTransport_CenterSequenceData_regular_compact
import Theorems.Thm_OAI_WeakMTWTransport_CenterSequenceData_true_ray_compact
import Theorems.Thm_OAI_WeakMTWTransport_MaximumDiagonal_center_matrix_limit
import Theorems.Thm_OAI_WeakMTWTransport_MaximumDiagonal_scalar_jets
import Theorems.Thm_OAI_WeakMTWTransport_MaximumJensenFamily_center_regular
import Theorems.Thm_OAI_WeakMTWTransport_exists_true_center_limit

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma continuous_scalar_family_deriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (fun p:ℝ×ℝ=>deriv (fun s=>Φ (p.1,s)) p.2) := by
  have heq (p:ℝ×ℝ) := (scalar_family_hasDeriv hΦ p).deriv
  simp_rw [heq]
  exact (contDiff_infty_iff_fderiv.mp hΦ).2.continuous.clm_apply continuous_const

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarSecond
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

lemma contDiff_scalar_family_deriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun p:ℝ×ℝ=>deriv (fun s=>Φ (p.1,s)) p.2) := by
  have heq (p:ℝ×ℝ) := (scalar_family_hasDeriv hΦ p).deriv
  simp_rw [heq]
  exact (contDiff_infty_iff_fderiv.mp hΦ).2.clm_apply contDiff_const

lemma continuous_scalar_family_second {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (fun p:ℝ×ℝ=>iteratedDeriv 2 (fun s=>Φ (p.1,s)) p.2) := by
  have H:=continuous_scalar_family_deriv (contDiff_scalar_family_deriv hΦ)
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MovingPrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma movingPrefix_contMDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (Function.uncurry (movingPrefix a t)) (b,p) := by
  exact (movingNormal_contMDiffAt (q := (b,t • p)) hb).comp (b,p)
    (contDiffAt_fst.prodMk (contDiffAt_snd.const_smul t)).contMDiffAt

lemma movingPrefixChart_contDiffAt {a c : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingPrefixChart a c t)) (b,p) := by
  exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n)) (by simpa only [extChartAt_source,Function.uncurry] using hc)) |>.comp (b,p)
      (movingPrefix_contMDiffAt hb)).contDiffAt

lemma movingPrefixEnergy_contDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ContDiffAt ℝ ∞ (Function.uncurry (movingPrefixEnergy a t)) (b,p) := by
  have hA : ContMDiffAt 𝓘(ℝ,Model n×Model n) 𝓘(ℝ,Model n) ∞
      (fun q:Model n×Model n=> movingNormal a (q.1,0)) (b,p) :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp (b,p)
      (contDiffAt_fst.prodMk contDiffAt_const).contMDiffAt
  have hC := cost_contMDiffAt_of_injectivityDomain
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm b,
      t • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hC' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q:M×M=>cost q.1 q.2) (movingNormal a (b,0),movingPrefix a t b p) := by
    simpa only [movingNormal_zero hb,movingPrefix_eq hb] using hC
  exact ((hC'.comp (b,p) (hA.prodMk (movingPrefix_contMDiffAt hb))).contDiffAt.div_const t)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_GraphCoordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] in
lemma graph_coordinates_at_center (q : TangentBundle 𝓘(ℝ,Model n) M) :
    graphVelocityCoordinate q.1 q=q.2 := by
  unfold graphVelocityCoordinate
  rw [tangent_chart_apply]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source q.1)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActiveGraphLimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartFiberInverse_at_center (a : M) (p : Model n) :
    chartFiberInverse a ((extChartAt 𝓘(ℝ,Model n) a) a) p=p := by
  dsimp only [chartFiberInverse]
  rw [(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source (Model n) a)]
  exact tangentCoordChange_self (I := 𝓘(ℝ,Model n)) (mem_extChartAt_source a)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveDifferentiability
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma activeLog_derivative_eq {v : M → ℝ} (hv : Continuous v) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ activeLogs v x)
    {D : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun h => cTransform v (riemannianExp x h)) D 0) :
    D = innerSL ℝ p := by
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
    cTransform v (riemannianExp x h) + 2 * normalCost x ((1/2:ℝ) • p) h
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro h
    have hh := active_split_lower_support hv hp.1 hp.2
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (riemannianExp x h)
    dsimp [f,normalCost]
    rw [riemannianExp_zero]
    linarith
  have hf : HasFDerivAt f (D - innerSL ℝ p) 0 := by
    apply (hD.add ((normalCost_hasFDerivAt_zero hID).const_mul 2)).congr_fderiv
    ext h
    simp only [_root_.add_apply,_root_.sub_apply,
      _root_.smul_apply,innerSL_apply_apply,inner_neg_left,
      real_inner_smul_left,smul_eq_mul]
    ring
  exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hf)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Taylor
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

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasQuadraticExpansion.hasFDerivAt {f : E → ℝ} {p : E} {A : E →L[ℝ] E}
    (hexp : HasQuadraticExpansion f p A) : HasFDerivAt f ((innerSL ℝ) p) 0 := by
  obtain ⟨d,hd,hbound⟩ := hexp 1 zero_lt_one
  let K : ℝ := 1+‖A‖/2
  have hK : 0 < K := by dsimp [K] <;> positivity
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro c hc
  have hpos : 0 < min d (c/K) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0:E) hpos] with h hh
  have hn : ‖h‖ < min d (c/K) := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have hb := hbound h (lt_of_lt_of_le hn (min_le_left _ _))
  have hA : |inner ℝ (A h) h| ≤ ‖A‖*‖h‖^2 := by
    calc
      _ ≤ ‖A h‖*‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A‖*‖h‖)*‖h‖ := mul_le_mul_of_nonneg_right (A.le_opNorm h) (norm_nonneg _)
      _ = _ := by ring
  have heq : f h-f 0-inner ℝ p h =
      (f h-quadraticTaylor (f 0) p A h)+inner ℝ (A h) h/2 := by
    simp only [quadraticTaylor]
    ring
  have hb' : |f h-f 0-inner ℝ p h| ≤ K*‖h‖^2 := by
    rw [heq]
    have ht := abs_add_le (f h-quadraticTaylor (f 0) p A h) (inner ℝ (A h) h/2)
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at ht
    dsimp [K]
    nlinarith
  have hmul : ‖h‖*K ≤ c := (le_div_iff₀ hK).mp (le_of_lt (lt_of_lt_of_le hn (min_le_right _ _)))
  have hbc : K*‖h‖^2 ≤ c*‖h‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hmul (norm_nonneg h)]
  simpa only [zero_add,innerSL_apply_apply,Real.norm_eq_abs] using hb'.trans hbc

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_TrueCenterGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma NormalAlexandrovContact.active_eq {u:M → ℝ} (hu:Continuous u) {y:M}
    {p r:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A) (hr:r∈activeLogs u y) : r=p := by
  have H:=activeLog_derivative_eq hu hr hA.2.2.2.hasFDerivAt
  apply ext_inner_right ℝ
  intro d
  exact (congrArg (fun L:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ=>L d) H).symm

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma TrueCenterRow.active {c:M} {u v:M → ℝ} (hdual:IsCostDualPair u v)
    {φ:ℝ → ℝ} {x:Model n} {z:M} {τ l:ℝ} (R:TrueCenterRow c u v φ x z τ l) :
    chartFiberInverse c x R.r∈activeLogs u ((extChartAt 𝓘(ℝ,Model n) c).symm x) := by
  refine ⟨R.minimizing,?_⟩
  have H:=R.contact
  rw [movingNormal_eq R.chart] at H
  simpa only [contactGap,hdual.2,chartFiberInverse] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ShortEnvelopeJetTest
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

lemma secondJetPullback_tendsto {ι : Type*} {L : Filter ι}
    {j : ι → F →L[ℝ] ℝ} {h : ι → F →L[ℝ] F →L[ℝ] ℝ}
    {m : ι → E →L[ℝ] F} {r : ι → E →L[ℝ] E →L[ℝ] F}
    {j₀ : F →L[ℝ] ℝ} {h₀ : F →L[ℝ] F →L[ℝ] ℝ}
    {m₀ : E →L[ℝ] F} {r₀ : E →L[ℝ] E →L[ℝ] F}
    (hj : Tendsto j L (𝓝 j₀)) (hh : Tendsto h L (𝓝 h₀))
    (hm : Tendsto m L (𝓝 m₀)) (hr : Tendsto r L (𝓝 r₀)) :
    Tendsto (fun i => secondJetPullback (j i) (h i) (m i) (r i)) L
      (𝓝 (secondJetPullback j₀ h₀ m₀ r₀)) := by
  let : NormedAddCommGroup (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  have hm' := (((ContinuousLinearMap.compL ℝ E F ℝ).flip).continuous.tendsto m₀).comp hm
  have hh' := ((ContinuousLinearMap.compL ℝ E F (F →L[ℝ] ℝ)).continuous₂.tendsto (h₀,m₀)).comp
    (hh.prodMk_nhds hm)
  have hfirst := ((ContinuousLinearMap.compL ℝ E (F →L[ℝ] ℝ) (E →L[ℝ] ℝ)).continuous₂.tendsto
    (((ContinuousLinearMap.compL ℝ E F ℝ).flip) m₀,h₀.comp m₀)).comp (hm'.prodMk_nhds hh')
  have hj' := ((ContinuousLinearMap.compL ℝ E F ℝ).continuous.tendsto j₀).comp hj
  have hsecond := ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] F) (E →L[ℝ] ℝ)).continuous₂.tendsto
    (ContinuousLinearMap.compL ℝ E F ℝ j₀,r₀)).comp (hj'.prodMk_nhds hr)
  exact hfirst.add hsecond

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_BilinearClose
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma bilinear_quadratic_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (d:E) : |A d d|≤‖A‖*‖d‖^2 := by
  calc
    |A d d| = ‖A d d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖A d‖*‖d‖ := (A d).le_opNorm d
    _ ≤ (‖A‖*‖d‖)*‖d‖ := mul_le_mul_of_nonneg_right (A.le_opNorm d) (norm_nonneg d)
    _ = ‖A‖*‖d‖^2 := by ring

lemma bilinear_quadratic_close {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E →L[ℝ] E →L[ℝ] ℝ} {ε:ℝ} (h : ‖A-B‖≤ε) (d:E) :
    A d d≤B d d+ε*‖d‖^2 := by
  have H := (le_abs_self ((A-B) d d)).trans (bilinear_quadratic_norm_bound (A-B) d)
  have HH := H.trans (mul_le_mul_of_nonneg_right h (sq_nonneg ‖d‖))
  simpa only [_root_.sub_apply,sub_le_iff_le_add,add_comm] using HH

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FrameMetric
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section FrameMetric
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma frameMetric_continuousAt {a:M} {b:Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) : ContinuousAt (frameMetric a) b := by
  have hp : (1:ℝ) • chartFiberInverse a b 0∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    simpa only [map_zero,smul_zero] using zero_mem_injectivityDomain
      (n := n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)
  have H := (ContDiffAt.partial_snd_fderiv_two (movingPrefixEnergy_contDiffAt hb hp)).continuousAt
  exact ContinuousAt.comp (f := fun z:Model n=>(z,(0:Model n))) H
    (show ContinuousAt (fun z:Model n=>(z,(0:Model n))) b from
    continuousAt_id.prodMk continuousAt_const)

end FrameMetric
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ChartTrueMatrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ChartTrueMatrix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma chartJetMatrix_tendsto {a c:M} {b q:ℕ → Model n} {b0 q0:Model n}
    {p:ℕ → Model n →L[ℝ] ℝ} {p0:Model n →L[ℝ] ℝ}
    {A:ℕ → Model n →L[ℝ] Model n →L[ℝ] ℝ} {A0:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hb0:b0∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc:movingPrefix a 1 b0 q0∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hb:Tendsto b atTop (𝓝 b0)) (hq:Tendsto q atTop (𝓝 q0))
    (hp:Tendsto p atTop (𝓝 p0)) (hA:Tendsto A atTop (𝓝 A0)) :
    Tendsto (fun k=>chartJetMatrix a c (b k) (q k) (p k) (A k)) atTop
      (𝓝 (chartJetMatrix a c b0 q0 p0 A0)) := by
  let : NormedAddCommGroup (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (Model n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  have hg:=movingPrefixChart_contDiffAt hb0 hc
  have hbx:=hb.prodMk_nhds hq
  have hD:=((ContDiffAt.partial_snd_fderiv hg).continuousAt.tendsto).comp hbx
  have hD2:=((ContDiffAt.partial_snd_fderiv_two hg).continuousAt.tendsto).comp hbx
  have hf : Tendsto (fun k=>frameMetric a (b k)) atTop (𝓝 (frameMetric a b0)) :=
    (frameMetric_continuousAt hb0).tendsto.comp hb
  have hs : Tendsto (fun k=>secondJetPullback (p k) (A k)
      (fderiv ℝ (movingPrefixChart a c 1 (b k)) (q k))
      (fderiv ℝ (fderiv ℝ (movingPrefixChart a c 1 (b k))) (q k))) atTop
      (𝓝 (secondJetPullback p0 A0 (fderiv ℝ (movingPrefixChart a c 1 b0) q0)
        (fderiv ℝ (fderiv ℝ (movingPrefixChart a c 1 b0)) q0))) :=
    secondJetPullback_tendsto hp hA hD hD2
  exact hf.add hs
end ChartTrueMatrix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MovingHessianLimit
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
variable {Q E F : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tendsto_clm_apply {ι : Type*} {l : Filter ι}
    {A : ι → E →L[ℝ] F} {v : ι → E} {A₀ : E →L[ℝ] F} {v₀ : E}
    (hA : Tendsto A l (𝓝 A₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i=>A i (v i)) l (𝓝 (A₀ v₀)) := by
  have hc : Continuous (fun q:(E →L[ℝ] F)×E => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (hc.tendsto (A₀,v₀)).comp (hA.prodMk_nhds hv)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterRayLimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section CenterRayLimit
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma chartRay_at_center (c:M) (r:Model n) :
    chartRay c (extChartAt 𝓘(ℝ,Model n) c c) r=⟨c,r⟩ := by
  simp only [chartRay,chartFiberInverse_at_center]
  exact congrArg (fun y:M=>(⟨y,r⟩:TangentBundle 𝓘(ℝ,Model n) M))
    ((extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c))

lemma chartRay_tendsto {c:M} {b r:ℕ → Model n} {r0:Model n}
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr:Tendsto r atTop (𝓝 r0)) :
    Tendsto (fun k=>chartRay c (b k) (r k)) atTop
      (𝓝 (⟨c,r0⟩:TangentBundle 𝓘(ℝ,Model n) M)) := by
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨c,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hc:extChartAt 𝓘(ℝ,Model n) c c∈(extChartAt 𝓘(ℝ,Model n) c).target:=
    (extChartAt 𝓘(ℝ,Model n) c).map_source (mem_extChartAt_source c)
  have ht:(extChartAt 𝓘(ℝ,Model n) c c,r0)∈χ.target:=
    (tangent_chart_target_iff _ _).mpr hc
  have H: Tendsto (fun k=>χ.symm (b k,r k)) atTop
      (𝓝 (χ.symm (extChartAt 𝓘(ℝ,Model n) c c,r0))):=
    (continuousAt_extChartAt_symm'' ht).tendsto.comp (hb.prodMk_nhds hr)
  rw [tangent_chart_symm_trivialization hc] at H
  change Tendsto _ _ (𝓝 (chartRay c (extChartAt 𝓘(ℝ,Model n) c c) r0)) at H
  rw [chartRay_at_center] at H
  apply H.congr'
  filter_upwards [hb.eventually ((isOpen_extChartAt_target _).mem_nhds hc)] with k hk
  exact tangent_chart_symm_trivialization hk

section
variable [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma modified_reverseRay_tendsto {c:M} {b r:ℕ → Model n} {l:ℕ → ℝ} {r0:Model n} {l0:ℝ}
    (hb:Tendsto b atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)))
    (hr:Tendsto r atTop (𝓝 r0)) (hl:Tendsto l atTop (𝓝 l0)) :
    Tendsto (fun k=>reverseRay (tangentScale (l k) (chartRay c (b k) (r k)))) atTop
      (𝓝 (reverseRay (⟨c,l0 • r0⟩:TangentBundle 𝓘(ℝ,Model n) M))) := by
  exact continuous_reverseRay.continuousAt.tendsto.comp
    (contMDiff_tangentScale.continuous.continuousAt.tendsto.comp
      (hl.prodMk_nhds (chartRay_tendsto hb hr)))

end

lemma graph_coordinates_tendsto {q:ℕ → TangentBundle 𝓘(ℝ,Model n) M}
    {q0:TangentBundle 𝓘(ℝ,Model n) M} (hq:Tendsto q atTop (𝓝 q0)) :
    Tendsto (fun k=>graphBaseCoordinate q0.1 (q k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) q0.1 q0.1)) ∧
    Tendsto (fun k=>graphVelocityCoordinate q0.1 (q k)) atTop (𝓝 q0.2) := by
  let χ:=extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨q0.1,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hs:q0∈χ.source:=(tangent_chart_source_iff _ _).mpr (mem_extChartAt_source _)
  have H:=((continuousOn_extChartAt _).continuousAt
    ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp hq
  have HV:Tendsto (fun k=>graphVelocityCoordinate q0.1 (q k)) atTop
      (𝓝 (graphVelocityCoordinate q0.1 q0)):=H.snd_nhds
  rw [graph_coordinates_at_center] at HV
  exact ⟨H.fst_nhds,HV⟩

end CenterRayLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_JointMovingPrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section JointMovingPrefix
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma joint_movingPrefix_contMDiffAt {a : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,(ℝ×Model n)×Model n) 𝓘(ℝ,Model n) ∞
      (fun q : (ℝ×Model n)×Model n=>movingPrefix a q.1.1 q.1.2 q.2) ((t,b),p) := by
  exact (movingNormal_contMDiffAt (q := (b,t • p)) hb).comp ((t,b),p)
    (contDiffAt_fst.snd.prodMk (contDiffAt_fst.fst.smul contDiffAt_snd)).contMDiffAt

lemma joint_movingPrefixChart_contDiffAt {a c : M} {t : ℝ} {b p : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hc : movingPrefix a t b p∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    ContDiffAt ℝ ∞
      (fun q : (ℝ×Model n)×Model n=>movingPrefixChart a c q.1.1 q.1.2 q.2) ((t,b),p) := by
  exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,Model n))
    (by simpa only [extChartAt_source] using hc)).comp ((t,b),p)
      (joint_movingPrefix_contMDiffAt hb)).contDiffAt

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma movingPrefix_at_center (a : M) (t : ℝ) (p : Model n) :
    movingPrefix a t (extChartAt 𝓘(ℝ,Model n) a a) p=riemannianExp a (t • p) := by
  have hb := (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  rw [movingPrefix_eq hb]
  change riemannianExp _ (t • chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a) p)=_
  rw [chartFiberInverse_at_center,(extChartAt 𝓘(ℝ,Model n) a).left_inv (mem_extChartAt_source a)]
  rfl

end JointMovingPrefix
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_OriginalCenterLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section OriginalCenterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance originalLimitFinite_r24babb_1 (x:M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
local instance originalLimitDualGroup_r24babb_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance originalLimitDualSpace_r24babb_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance originalLimitBilinearGroup_r24babb_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance originalLimitBilinearSpace_r24babb_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma exists_original_center_limit : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(u:M → ℝ) (a c:M) (φ:ℕ → ℝ → ℝ) (lj:ℕ → ℝ) (yj:ℕ → M),
    ∀(pj:(j:ℕ) → TangentSpace 𝓘(ℝ,Model n) (yj j))
      (Aj:(j:ℕ) → TangentSpace 𝓘(ℝ,Model n) (yj j) →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (yj j))
      (sj:ℕ → Model n) (Sj:ℕ → Model n →L[ℝ] Model n),
    ∀(l κ χ:ℝ) (q r:Model n) (g:Model n →L[ℝ] ℝ) (H:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    l∈U → 0<l → l<1 → 0<χ →
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈injectivityDomain a → riemannianExp a q=c →
    Tendsto lj atTop (𝓝 l) →
    Tendsto (fun j=>(⟨yj j,pj j⟩:TangentBundle 𝓘(ℝ,Model n) M)) atTop
      (𝓝 (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto (fun j=>reverseRay (⟨yj j,lj j • pj j⟩:TangentBundle 𝓘(ℝ,Model n) M)) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto (fun j=>iteratedDeriv 2 (φ j) (cTransform u (yj j))) atTop (𝓝 κ) →
    Tendsto (fun j=>innerSL ℝ (sj j)) atTop (𝓝 g) →
    Tendsto (fun j=>(innerSL ℝ).comp (Sj j)) atTop (𝓝 H) →
    (∀ᶠ j in atTop,NormalAlexandrovContact (n:=n) u (yj j) (pj j) (Aj j) ∧
      (∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator (yj j) (pj j)+Aj j) d) d) ∧
      χ≤expJacobian (yj j) (pj j)*(normalHessianOperator (yj j) (pj j)+Aj j).det ∧
      ContDiffAt ℝ 2 (φ j) (cTransform u (yj j)) ∧
      deriv (φ j) (cTransform u (yj j))=lj j ∧
      (∀d e,inner ℝ (Sj j d) e=inner ℝ d (Sj j e)) ∧
      HasQuadraticExpansion (fun h=>φ j (cTransform u ((extChartAt 𝓘(ℝ,Model n) c).symm
        (extChartAt 𝓘(ℝ,Model n) c (yj j)+h)))) (sj j) (Sj j)) →
    ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (κ/l^2)*(frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤
          chartJetMatrix a c (extChartAt 𝓘(ℝ,Model n) a a) q g H d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  classical
  obtain ⟨δ,hδ,U,hU,h1,Hδ⟩:=exists_true_center_limit (n:=n) (M:=M)
  refine ⟨δ,hδ,U,hU,h1,?_⟩
  intro u a c φ lj yj pj Aj sj Sj l κ χ q r g H hlu hl hl1 hχ hq he hlj hfull hshort hκ hg hH hgood
  let z:=fun j=>reverseRay (⟨yj j,lj j • pj j⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hy:Tendsto yj atTop (𝓝 c):=
    (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).continuousAt.tendsto.comp hfull
  have hz:Tendsto (fun j=>(z j).1) atTop (𝓝 a):=
    (FiberBundle.continuous_proj (Model n) (TangentSpace 𝓘(ℝ,Model n))).continuousAt.tendsto.comp hshort
  have hccharts:=hy.eventually ((isOpen_extChartAt_source (I:=𝓘(ℝ,Model n)) c).mem_nhds (mem_extChartAt_source c))
  have hacharts:=hz.eventually ((isOpen_extChartAt_source (I:=𝓘(ℝ,Model n)) a).mem_nhds (mem_extChartAt_source a))
  have hpos:=hlj.eventually (Ioo_mem_nhds hl hl1)
  obtain ⟨N,hN⟩:=eventually_atTop.mp (hgood.and (hpos.and (hccharts.and hacharts)))
  let σ:=fun j:ℕ=>j+N
  have hσ:Tendsto σ atTop atTop:=tendsto_add_atTop_nat N
  have hn (j:ℕ):N≤σ j:=Nat.le_add_left _ _
  let J (j:ℕ):TrueCenterJet (n:=n) u a c (φ (σ j)) (lj (σ j)):=
    trueCenterJetOfOriginal (hN _ (hn j)).1.1 (hN _ (hn j)).1.2.1
      (hN _ (hn j)).2.1.1 (hN _ (hn j)).2.1.2
      (hN _ (hn j)).2.2.1 (hN _ (hn j)).2.2.2
      (hN _ (hn j)).1.2.2.2.1 (hN _ (hn j)).1.2.2.2.2.1
      (hN _ (hn j)).1.2.2.2.2.2.1 (hN _ (hn j)).1.2.2.2.2.2.2
  obtain ⟨hb,hqq⟩:=graph_coordinates_tendsto hshort
  have hbj:Tendsto (fun j=>(J j).b) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)):=hb.comp hσ
  have hqj:Tendsto (fun j=>(J j).q) atTop (𝓝 q):=hqq.comp hσ
  have hc:movingPrefix a 1 (extChartAt 𝓘(ℝ,Model n) a a) q∈(extChartAt 𝓘(ℝ,Model n) c).source:=by
    rw [movingPrefix_at_center,one_smul,he]
    exact mem_extChartAt_source c
  have hmatrix:Tendsto (fun j=>(J j).matrix) atTop
      (𝓝 (chartJetMatrix a c (extChartAt 𝓘(ℝ,Model n) a a) q g H)):=
    chartJetMatrix_tendsto (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) a) hc hbj hqj (hg.comp hσ) (hH.comp hσ)
  exact Hδ u a c (φ ∘ σ) (lj ∘ σ) J l κ χ q r _ hlu hl hl1 hχ hq
    (hlj.comp hσ) hbj hqj (hfull.comp hσ) (hκ.comp hσ) hmatrix
    (Eventually.of_forall (fun j=>(hN _ (hn j)).1.2.2.1))
end OriginalCenterLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CenterSequenceOriginalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section CenterSequenceOriginalLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance sequenceOrigDualGroup_r24babb_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance sequenceOrigDualSpace_r24babb_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance sequenceOrigBilinearGroup_r24babb_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance sequenceOrigBilinearSpace_r24babb_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
omit [MeasurableSpace M] [BorelSpace M] in
lemma exists_center_sequence_original_limit : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(a c:M) (u v:M → ℝ) (Φ:ℝ×ℝ → ℝ) (γ l χ:ℝ),
    Continuous u → Continuous v → IsCostDualPair u v → ContDiff ℝ ∞ Φ →
    deriv (fun s=>Φ (γ,s)) (v c)=l → l∈U → 0<l → l<1 → 0<χ →
    ∀(γj lj τj tj:ℕ → ℝ) (xj bj qj:ℕ → Model n) (zj:ℕ → M) (F:ℕ → Model n → ℝ),
    CenterSequenceData a c u v Φ γj lj τj tj xj bj qj zj F →
    ∀q:Model n,
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
    Tendsto γj atTop (𝓝 γ) → Tendsto lj atTop (𝓝 l) →
    Tendsto τj atTop (𝓝 0) → Tendsto tj atTop (𝓝 1) →
    Tendsto xj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) →
    Tendsto bj atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) →
    (∀ᶠ j in atTop,0<τj j) → ∀L:ℝ≥0,
    (∀ᶠ j in atTop,LipschitzWith L (fun y=>Φ (γj j,v y))) →
    ∀(sj:ℕ → Model n) (Sj:ℕ → Model n →L[ℝ] Model n)
      (g:Model n →L[ℝ] ℝ) (H:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun j=>innerSL ℝ (sj j)) atTop (𝓝 g) →
    Tendsto (fun j=>(innerSL ℝ).comp (Sj j)) atTop (𝓝 H) →
    (∀ᶠ j in atTop,OriginalCenterGood (n:=n) u χ ((extChartAt 𝓘(ℝ,Model n) c).symm (xj j)) ∧
      deriv (fun s=>Φ (γj j,s)) (v ((extChartAt 𝓘(ℝ,Model n) c).symm (xj j)))=lj j ∧
      (∀d e,inner ℝ (Sj j d) e=inner ℝ d (Sj j e)) ∧
      HasQuadraticExpansion (fun h=>Φ (γj j,v ((extChartAt 𝓘(ℝ,Model n) c).symm (xj j+h)))) (sj j) (Sj j)) →
    ∃r:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      reverseRay (⟨c,l • r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
      ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (iteratedDeriv 2 (fun s=>Φ (γ,s)) (v c)/l^2)*
          (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤
            chartJetMatrix a c (extChartAt 𝓘(ℝ,Model n) a a) q g H d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  classical
  let : T2Space (TangentBundle 𝓘(ℝ,Model n) M) := bundle_totalSpace_t2
  obtain ⟨δ,hδ,U,hU,h1,Hδ⟩:=exists_original_center_limit (n:=n) (M:=M)
  refine ⟨δ,hδ,U,hU,h1,?_⟩
  intro a c u v Φ γ l χ hu hv hd hΦ hder hlu hl hl1 hχ γj lj τj tj xj bj qj zj F D q hq he
    hγ hlm hτ ht hx hb hτpos L hLip sj Sj g H hg hH hgood
  let yj:=fun j=>(extChartAt 𝓘(ℝ,Model n) c).symm (xj j)
  let pj (j:ℕ):TangentSpace 𝓘(ℝ,Model n) (yj j):=
    if h:OriginalCenterGood (n:=n) u χ (yj j) then Classical.choose h else 0
  let Aj (j:ℕ):TangentSpace 𝓘(ℝ,Model n) (yj j) →L[ℝ] TangentSpace 𝓘(ℝ,Model n) (yj j):=
    if h:OriginalCenterGood (n:=n) u χ (yj j) then Classical.choose (Classical.choose_spec h) else 0
  have hPA:∀ᶠ j in atTop,NormalAlexandrovContact (n:=n) u (yj j) (pj j) (Aj j) ∧
      (∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator (yj j) (pj j)+Aj j) d) d) ∧
      χ≤expJacobian (yj j) (pj j)*(normalHessianOperator (yj j) (pj j)+Aj j).det:=by
    filter_upwards [hgood] with j hj
    have hj0 : OriginalCenterGood (n:=n) u χ (yj j) := hj.1
    simpa only [pj,Aj,dite_eq_left hj0] using Classical.choose_spec (Classical.choose_spec hj0)
  have hray:∀ᶠ j in atTop,(⟨yj j,pj j⟩:TangentBundle 𝓘(ℝ,Model n) M)=chartRay c (xj j) (D.row j).r:=by
    filter_upwards [hPA] with j hj
    exact congrArg (fun p:TangentSpace 𝓘(ℝ,Model n) (yj j)=>
      (⟨yj j,p⟩:TangentBundle 𝓘(ℝ,Model n) M))
      ((hj.1.active_eq hu ((D.row j).active hd)).symm)
  obtain ⟨σ,hσ,r,hr,hrr,hshort⟩:=D.true_ray_compact hv (hΦ.contDiffAt) hder hl hl1 hq he
    hγ hlm hτ ht hx hb hτpos L hLip
  have hreg:=D.regular_compact hv hΦ.contDiffAt hder hl hl1 hq he hγ hlm hτ ht hx hb hτpos L hLip
  have hfull:Tendsto (fun j=>(⟨yj (σ j),pj (σ j)⟩:TangentBundle 𝓘(ℝ,Model n) M)) atTop
      (𝓝 (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)):=
    (chartRay_tendsto (hx.comp hσ.tendsto_atTop) hrr).congr'
      (Filter.EventuallyEq.symm (hσ.tendsto_atTop.eventually hray))
  have hshort':Tendsto (fun j=>reverseRay (⟨yj (σ j),lj (σ j) • pj (σ j)⟩:TangentBundle 𝓘(ℝ,Model n) M)) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)):=by
    apply hshort.congr'
    filter_upwards [hσ.tendsto_atTop.eventually hray] with j hj
    exact congrArg (fun w:TangentBundle 𝓘(ℝ,Model n) M=>reverseRay (tangentScale (lj (σ j)) w)) hj.symm
  have hrev:reverseRay (⟨c,l • r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩:=
    tendsto_nhds_unique (modified_reverseRay_tendsto (hx.comp hσ.tendsto_atTop) hrr
      (hlm.comp hσ.tendsto_atTop)) hshort
  have hy:Tendsto yj atTop (𝓝 c):=by
    have HH:=(continuousAt_extChartAt_symm'' (mem_extChartAt_target (I:=𝓘(ℝ,Model n)) c)).tendsto.comp hx
    rwa [(extChartAt 𝓘(ℝ,Model n) c).left_inv (mem_extChartAt_source c)] at HH
  have hvy:Tendsto (fun j=>v (yj j)) atTop (𝓝 (v c)):=hv.continuousAt.tendsto.comp hy
  have hκ:=((continuous_scalar_family_second hΦ).tendsto (γ,v c)).comp (hγ.prodMk_nhds hvy)
  have hgood':∀ᶠ j in atTop,NormalAlexandrovContact (n:=n) u (yj j) (pj j) (Aj j) ∧
      (∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator (yj j) (pj j)+Aj j) d) d) ∧
      χ≤expJacobian (yj j) (pj j)*(normalHessianOperator (yj j) (pj j)+Aj j).det ∧
      ContDiffAt ℝ 2 (fun s=>Φ (γj j,s)) (cTransform u (yj j)) ∧
      deriv (fun s=>Φ (γj j,s)) (cTransform u (yj j))=lj j ∧
      (∀d e,inner ℝ (Sj j d) e=inner ℝ d (Sj j e)) ∧
      HasQuadraticExpansion (fun h=>Φ (γj j,cTransform u ((extChartAt 𝓘(ℝ,Model n) c).symm
        (extChartAt 𝓘(ℝ,Model n) c (yj j)+h)))) (sj j) (Sj j):=by
    filter_upwards [hgood,hPA] with j hj hP
    refine ⟨hP.1,hP.2.1,hP.2.2,?_,?_,hj.2.2.1,?_⟩
    · exact ((hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
    · rw [←hd.2]
      exact hj.2.1
    · rw [←hd.2]
      dsimp only [yj]
      rw [(extChartAt 𝓘(ℝ,Model n) c).right_inv (D.row j).chart]
      exact hj.2.2.2
  refine ⟨r,hr,hrev,?_⟩
  apply Hδ u a c (fun j s=>Φ (γj (σ j),s)) (lj ∘ σ) (yj ∘ σ)
    (fun j=>pj (σ j)) (fun j=>Aj (σ j)) (sj ∘ σ) (Sj ∘ σ)
    l _ χ q r g H hlu hl hl1 hχ hreg he (hlm.comp hσ.tendsto_atTop) hfull hshort'
  · rw [←hd.2]
    exact hκ.comp hσ.tendsto_atTop
  · exact hg.comp hσ.tendsto_atTop
  · exact hH.comp hσ.tendsto_atTop
  · exact hσ.tendsto_atTop.eventually hgood'
end CenterSequenceOriginalLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_Diagonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma diagonal_tendsto_of_close {X : Type*} [PseudoMetricSpace X]
    {f a : ℕ → X} {x : X} {ε : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hε : Tendsto ε atTop (𝓝 0))
    (hclose : ∀ᶠ k in atTop,dist (f k) (a k)≤ε k) : Tendsto f atTop (𝓝 x) := by
  apply tendsto_of_tendsto_of_dist ha
  exact squeeze_zero' (Eventually.of_forall (fun _=>dist_nonneg)) (hclose.mono (fun k hk=>by simpa only [dist_comm] using hk)) hε

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma MaximumFamily.limit_coordinates {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    (F : MaximumFamily (n := n) v α D bminus bplus Bc Bo)
    {Q:TangentBundle 𝓘(ℝ,Model n) M}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 Q)) :
    Tendsto (fun k=>graphBaseCoordinate Q.1 (F.row k).q.1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) Q.1 Q.1)) ∧
    Tendsto (fun k=>graphVelocityCoordinate Q.1 (F.row k).q.1) atTop (𝓝 (show Model n from Q.2)) ∧
    Tendsto F.z atTop (𝓝 (riemannianExp Q.1 Q.2)) ∧
    Tendsto (fun k=>riemannianExp (F.row k).q.1.1 (F.row k).q.1.2) atTop
      (𝓝 (riemannianExp Q.1 Q.2)) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (⟨Q.1,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hs : Q∈χ.source := (tangent_chart_source_iff _ _).mpr (mem_extChartAt_source Q.1)
  have HC := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp hQ
  have hvel : Tendsto (fun k=>graphVelocityCoordinate Q.1 (F.row k).q.1) atTop
      (𝓝 (graphVelocityCoordinate Q.1 Q)) := HC.snd_nhds
  rw [graph_coordinates_at_center] at hvel
  have HE := contMDiff_riemannianExp.continuous.tendsto Q |>.comp hQ
  have HP := (contMDiff_riemannianExp.continuous.comp contMDiff_tangentScale.continuous).tendsto (1,Q)
    |>.comp (F.time.prodMk_nhds hQ)
  have HZ : Tendsto F.z atTop (𝓝 (riemannianExp Q.1 Q.2)) := by
    change Tendsto (fun k=>riemannianExp (F.row k).q.1.1 (F.t k • (F.row k).q.1.2)) atTop
      (𝓝 (riemannianExp Q.1 ((1:ℝ) • Q.2))) at HP
    simp only [one_smul] at HP
    exact HP.congr (fun k=>(F.row k).projection)
  exact ⟨HC.fst_nhds,hvel,HZ,HE⟩
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.limits (J : MaximumJensenFamily hmtw hv ho F a c N)
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hε : Tendsto ε atTop (𝓝 0)) {q : Model n}
    (hQ : Tendsto (fun k=>(F.row k).q.1) atTop
      (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M))) (hc : riemannianExp a q=c) :
    Tendsto (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)) ∧
    Tendsto (fun k=>graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1) atTop (𝓝 q) ∧
    Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) ∧
    Tendsto (fun k=>J.sampleGradient k (S.ν k)) atTop (𝓝 0) := by
  obtain ⟨hb,hp,hz,hy⟩ := F.limit_coordinates hQ
  rw [hc] at hy
  have hY := ((continuousOn_extChartAt _).continuousAt ((isOpen_extChartAt_source _).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℝ,Model n)) c))).tendsto.comp hy
  refine ⟨diagonal_tendsto_of_close hb hε (Eventually.of_forall (fun k=>(S.baseClose k).le)),
    diagonal_tendsto_of_close hp hε (Eventually.of_forall (fun k=>(S.velocityClose k).le)),
    diagonal_tendsto_of_close hY hε (Eventually.of_forall (fun k=>(S.centerClose k).le)),?_⟩
  apply diagonal_tendsto_of_close tendsto_const_nhds hε
  exact Eventually.of_forall (fun k=>by simpa only [dist_zero_right] using (S.gradientClose k).le)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumEndpoint
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.movingChart {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P) (k:ℕ) :
    movingPrefixChart a c (F.t k) (graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
      (graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1)=
        (J.sample k).z (J.sampleIndex k (S.ν k)) := by
  rw [movingPrefixChart,movingPrefix_graph_coordinates (S.poleSource k)]
  exact S.endpointChart k

lemma MaximumDiagonal.endpoint_tendsto {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    {q:Model n} (hc:riemannianExp a q=c)
    (hb:Tendsto (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) a a)))
    (hp:Tendsto (fun k=>graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1) atTop (𝓝 q)) :
    Tendsto (fun k=>(J.sample k).z (J.sampleIndex k (S.ν k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c)) := by
  have hb0:extChartAt 𝓘(ℝ,Model n) a a∈(extChartAt 𝓘(ℝ,Model n) a).target:=
    (extChartAt 𝓘(ℝ,Model n) a).map_source (mem_extChartAt_source a)
  have hgc:movingPrefix a 1 (extChartAt 𝓘(ℝ,Model n) a a) q∈(extChartAt 𝓘(ℝ,Model n) c).source := by
    rw [movingPrefix_at_center,one_smul,hc]
    exact mem_extChartAt_source c
  have H:=((joint_movingPrefixChart_contDiffAt hb0 hgc).continuousAt.tendsto).comp
    ((F.time.prodMk_nhds hb).prodMk_nhds hp)
  change Tendsto (fun k=>movingPrefixChart a c (F.t k)
    (graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
    (graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1)) atTop
    (𝓝 (movingPrefixChart a c 1 (extChartAt 𝓘(ℝ,Model n) a a) q)) at H
  simp only [S.movingChart] at H
  simpa only [movingPrefixChart,movingPrefix_at_center,one_smul,hc] using H

end MaximumEndpoint
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumCenterLimit
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.center_matrix_le_pole_limit {J:MaximumJensenFamily hmtw hv ho F a c N}
    {ε:ℕ → ℝ} {P:ℕ → ℕ → Prop} (S:MaximumDiagonal J ε P)
    (hε:Tendsto ε atTop (𝓝 0))
    {H L:Model n →L[ℝ] Model n →L[ℝ] ℝ}
    (hH:Tendsto (fun k=>J.sampleH k (S.ν k)) atTop (𝓝 H))
    (hL:Tendsto (fun k=>(J.first k).L) atTop (𝓝 L)) (d:Model n) : H d d ≤ L d d := by
  have hhh:Tendsto (fun k=>J.sampleH k (S.ν k) d d) atTop (𝓝 (H d d)):=tendsto_clm_apply (tendsto_clm_apply hH tendsto_const_nhds) tendsto_const_nhds
  have hll:Tendsto (fun k=>(J.first k).L d d) atTop (𝓝 (L d d)):=tendsto_clm_apply (tendsto_clm_apply hL tendsto_const_nhds) tendsto_const_nhds
  have HE:=hε.mul_const (‖d‖^2)
  have HI:∀ᶠ k in atTop,J.sampleH k (S.ν k) d d ≤ (J.first k).L d d+ε k*‖d‖^2:=by
    apply Eventually.of_forall
    intro k
    exact (bilinear_quadratic_close (S.HClose k).le d).trans
      (add_le_add ((J.first k).upper d) le_rfl)
  simpa only [zero_mul,add_zero] using le_of_tendsto_of_tendsto hhh (hll.add HE) HI
end MaximumCenterLimit
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumCenterSequence
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

lemma MaximumDiagonal.center_tendsto {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hx : Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    Tendsto (fun k=>(J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 c) := by
  let χ := extChartAt 𝓘(ℝ,Model n) c
  have H := (continuousAt_extChartAt_symm'' (χ.map_source (mem_extChartAt_source c))).tendsto.comp hx
  rw [χ.left_inv (mem_extChartAt_source c)] at H
  apply H.congr
  intro k
  exact χ.left_inv ((J.sample k).samples (J.sampleIndex k (S.ν k))).1

lemma MaximumDiagonal.slope_tendsto {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (hBc : ContDiff ℝ ∞ Bc) {β : ℝ} (hβ : Tendsto F.b atTop (𝓝 β))
    (hx : Tendsto (fun k=>J.sampleCenter k (S.ν k)) atTop
      (𝓝 (extChartAt 𝓘(ℝ,Model n) c c))) :
    Tendsto (fun k=>J.sampleSlope k (S.ν k)) atTop
      (𝓝 (deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c))) := by
  exact ((continuous_scalar_family_deriv (modifiedScalar_contDiff hBc α D)).tendsto (β,v c)).comp
    (hβ.prodMk_nhds ((hv.tendsto c).comp (S.center_tendsto hx)))

end MaximumCenterSequence
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumTrueCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumTrueCenter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance maximumTrueDualGroup_r24babb_1 : NormedAddCommGroup (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumTrueDualSpace_r24babb_1 : NormedSpace ℝ (Model n →L[ℝ] ℝ) := inferInstance
local instance maximumTrueBilinearGroup_r24babb_1 : NormedAddCommGroup (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
local instance maximumTrueBilinearSpace_r24babb_1 : NormedSpace ℝ (Model n →L[ℝ] Model n →L[ℝ] ℝ) := inferInstance
omit [MeasurableSpace M] [BorelSpace M] in
lemma exists_maximum_true_center_oai : ∃δ>0,∃U:Set ℝ,IsOpen U ∧ 1∈U ∧
    ∀(u v:M → ℝ),Continuous u → ∀Lv:ℝ≥0,∀hv:LipschitzWith Lv v,
    IsCostDualPair u v → ∀(α D bminus bplus A₀ B₀:ℝ) (Bc Bo:ℝ → ℝ),
    ∀ho:Continuous Bo,ContDiff ℝ ∞ Bc →
    (∀b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s))) →
    (∀y,v y∈Icc A₀ B₀) →
    (∀b∈Icc bminus bplus,∀y:M,0<deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y) ∧
      deriv (fun s=>modifiedScalar α D Bc (b,s)) (v y)<1) →
    ∀K:ℝ≥0,(∀b∈Icc bminus bplus,LipschitzWith K (modifiedDatum v α D b Bc)) →
    ∀hmtw:WeakMTW (n:=n) (M:=M),
    ∀F:MaximumFamily (n:=n) v α D bminus bplus Bc Bo,
    ∀(a c:M) (χ:ℝ) (N:Set (Model n)) (r₀:ℝ),0<χ → 0 < r₀ →
    (∀z∈ball (extChartAt 𝓘(ℝ,Model n) c c) r₀,z∉N →
      OriginalCenterGood (n:=n) u χ ((extChartAt 𝓘(ℝ,Model n) c).symm z) ∧
      ∃p:Model n,∃A:Model n →L[ℝ] Model n,
        (∀d e,inner ℝ (A d) e=inner ℝ d (A e)) ∧
        HasQuadraticExpansion (fun h=>v ((extChartAt 𝓘(ℝ,Model n) c).symm (z+h))) p A) →
    ∀J:MaximumJensenFamily hmtw hv.continuous ho F a c N,
    ∀(ε:ℕ → ℝ) (P:ℕ → ℕ → Prop) (S:MaximumDiagonal J ε P),
    Tendsto ε atTop (𝓝 0) → ∀(q:Model n) (β l:ℝ),
    (show TangentSpace 𝓘(ℝ,Model n) a from q)∈minimizingVectors a → riemannianExp a q=c →
    Tendsto (fun k=>(F.row k).q.1) atTop (𝓝 (⟨a,q⟩:TangentBundle 𝓘(ℝ,Model n) M)) →
    Tendsto F.b atTop (𝓝 β) → deriv (fun s=>modifiedScalar α D Bc (β,s)) (v c)=l →
    l∈U → 0<l → l<1 →
    ∀(g:Model n →L[ℝ] ℝ) (H L:Model n →L[ℝ] Model n →L[ℝ] ℝ),
    Tendsto (fun k=>fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c)
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 g) →
    Tendsto (fun k=>fderiv ℝ (fderiv ℝ
      (chartCenterEnvelope (modifiedDatum v α D (F.b k) Bc) (F.t k) c))
        ((J.sample k).z (J.sampleIndex k (S.ν k)))) atTop (𝓝 H) →
    Tendsto (fun k=>(J.first k).L) atTop (𝓝 L) →
    ∃r:Model n,(show TangentSpace 𝓘(ℝ,Model n) c from r)∈minimizingVectors c ∧
      reverseRay (⟨c,l • r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ ∧
      ∃V:Model n →L[ℝ] Model n →L[ℝ] ℝ,
      (∀d e,V d e=V e d) ∧ (∀d,d≠0 → 0<V d d) ∧
      (∀d,V d d+δ*(1-l)*frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) d d+
        (iteratedDeriv 2 (fun s=>modifiedScalar α D Bc (β,s)) (v c)/l^2)*
          (frameMetric a (extChartAt 𝓘(ℝ,Model n) a a) q d)^2≤L d d) ∧
      0<expJacobian c r ∧
      (chartFiberInverse a (extChartAt 𝓘(ℝ,Model n) a a)).toLinearMap.normDet^2*l^n*
        (expJacobian a q)^2*χ≤expJacobian c r*(bilinearOperator V).det := by
  obtain ⟨δ,hδ,U,hU,h1,Hδ⟩:=exists_center_sequence_original_limit (n:=n) (M:=M)
  refine ⟨δ,hδ,U,hU,h1,?_⟩
  intro u v hu Lv hv hd α D bminus bplus A₀ B₀ Bc Bo ho hBc hmono hrange hslope K hLip
    hmtw F a c χ N r₀ hχ hr₀ hgood J ε P S hε q β l hq he hQ hβ hder hlu hl hl1 g H L hg hH hL
  obtain ⟨hb,hp,hx,hgrad⟩:=S.limits J hε hQ he
  have hz:=S.endpoint_tendsto he hb hp
  obtain ⟨sj,Sj,hsj,hsg,hSH⟩:=S.scalar_jets hu hv hd hBc hmono hrange hslope hr₀ hgood hx hz hg hH
  have hls (k:ℕ):0<J.sampleSlope k (S.ν k) ∧ J.sampleSlope k (S.ν k)<1:=
    hslope _ (Ioo_subset_Icc_self (F.parameter k)) _
  let CD:=S.center_sequence hu hv hd hBc hmono hls hgrad
  have hlj:=S.slope_tendsto hBc hβ hx
  rw [hder] at hlj
  have hτ:Tendsto (fun k=>1-F.t k) atTop (𝓝 (0:ℝ)):=by
    simpa only [sub_self] using (tendsto_const_nhds.sub F.time:
      Tendsto (fun k=>(1:ℝ)-F.t k) atTop (𝓝 (1-1)))
  have hgood':∀ᶠ k in atTop,OriginalCenterGood (n:=n) u χ
      ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k))) ∧
      deriv (fun s=>modifiedScalar α D Bc (F.b k,s))
        (v ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k))))=J.sampleSlope k (S.ν k) ∧
      (∀d e,inner ℝ (Sj k d) e=inner ℝ d (Sj k e)) ∧
      HasQuadraticExpansion (fun h=>modifiedScalar α D Bc (F.b k,
        v ((extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k)+h)))) (sj k) (Sj k):=by
    filter_upwards [hsj] with k hk
    have hY:(extChartAt 𝓘(ℝ,Model n) c).symm (J.sampleCenter k (S.ν k))=
        (J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k))):=
      (extChartAt 𝓘(ℝ,Model n) c).left_inv ((J.sample k).samples (J.sampleIndex k (S.ν k))).1
    exact ⟨hY.symm ▸ hk.1,by rw [hY]; rfl,hk.2⟩
  obtain ⟨r,hr,hrev,V,hVs,hVp,hgain,hσ,hdet⟩:=Hδ a c u v (modifiedScalar α D Bc) β l χ
    hu hv.continuous hd (modifiedScalar_contDiff hBc α D) hder hlu hl hl1 hχ
    _ _ _ _ _ _ _ _ _ CD q hq he hβ hlj hτ F.time hx hb
    (Eventually.of_forall (fun k=>sub_pos.mpr (F.prefixTime k).2)) K
    (Eventually.of_forall (fun k=>hLip _ (Ioo_subset_Icc_self (F.parameter k))))
    sj Sj g H hsg hSH hgood'
  have hreg:=J.center_regular hu hv hd hBc hmono K hLip hq he hQ hβ hder hl hl1
  have hmat:=S.center_matrix_limit hε hreg he hQ hg hH
  refine ⟨r,hr,hrev,V,hVs,hVp,?_,hσ,hdet⟩
  intro d
  exact (hgain d).trans (S.center_matrix_le_pole_limit hε hmat hL d)
end MaximumTrueCenter
end WeakMTWTransport

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWTransport.exists_maximum_true_center_oai.{u_1} := @OAI.WeakMTWTransport.exists_maximum_true_center_oai.{u_1}
