-- Prove2me | solution 1 for OAI.Yau.Geometry.TripleSourceWaveData.uniform_rescaled_factor_jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:28:35.527197+00:00
-- url     : https://prove2.me/submissions/09a79414-47a8-48f3-a2d7-cc647c1832ba

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_TripleSourceWaveData_uniform_rescaled_phase_first

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_QuadraticChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma quadraticChartMap_zero (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    quadraticChartMap y e B 0 = y := by simp [quadraticChartMap]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricConnectionFamilyLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

variable {T : Type*} [TopologicalSpace T]
lemma positive_metric_inverse_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g)
    (hp : ∀ t, ∀ v : E, v ≠ 0 → 0 < g t v v) :
    Continuous (fun t ↦ ContinuousLinearMap.inverse (g t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (positiveMetricEquiv (g t) (hp t))).continuousAt
  have hc' : ContinuousAt
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (g t) := by
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  exact hc'.comp hg.continuousAt

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma christoffelCovector_continuous (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hD : Continuous D) : Continuous (fun t ↦ christoffelCovector (D t)) := by
  have hflip : Continuous (fun t ↦ (D t).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous.comp hD
  exact ((hD.add hflip).sub (hflip.const_clm_comp
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).const_smul (1/2:ℝ)

theorem metricConnection_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ)
    (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g) (hD : Continuous D)
    (hp : ∀ t, ∀ v : E, v ≠ 0 → 0 < g t v v) :
    Continuous (fun t ↦ metricConnection (g t) (D t)) := by
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).continuous.comp
    (positive_metric_inverse_continuous g hg hp)).clm_comp (christoffelCovector_continuous D hD)

theorem smooth_metric_connection_continuous (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y, ∀ v : E, v ≠ 0 → 0 < g y v v) :
    Continuous (fun y ↦ metricConnection (g y) (fderiv ℝ g y)) := by
  exact metricConnection_continuous g (fderiv ℝ g) hg.continuous
    (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hp

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PolynomialEvaluation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma reval_contDiff (p : CPoly) : ContDiff ℝ ∞ (reval p) := by
  change ContDiff ℝ ∞ (fun x ↦ reval p x)
  induction p using MvPolynomial.induction_on with
  | C a => simpa [reval] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Coord ↦ a))
  | add p q hp hq => simpa [reval] using hp.add hq
  | mul_X p i hp =>
    simpa [reval, coordCLM] using hp.mul (coordCLM i).contDiff

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FrameMapFamily
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable {T : Type*} [TopologicalSpace T]
lemma frameMap_continuous (e : T → Fin 4 → _root_.OAI.Yau.Jets.Coord) (he : ∀ i, Continuous (fun t ↦ e t i)) :
    Continuous (fun t ↦ frameMap (e t)) := by
  apply continuous_finsetSum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord (ContinuousLinearMap.proj i)).continuous.comp (he i)

theorem frameEquiv_continuous (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (e : T → Fin 4 → _root_.OAI.Yau.Jets.Coord) (he : ∀ i, Continuous (fun t ↦ e t i))
    (hortho : ∀ t i j, g t (e t i) (e t j) = if i = j then 1 else 0) :
    Continuous (fun t ↦ (frameEquiv (g t) (e t) (hortho t)).toContinuousLinearMap) :=
  frameMap_continuous e he

lemma frameConnection_continuous (B : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hB : Continuous B)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap)) :
    Continuous (fun t ↦ frameConnection (B t) (e t)) := by
  exact (((ContinuousLinearMap.compL ℝ _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord).flip.continuous.comp he).clm_comp hB).clm_comp he

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SpatialJetFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_spatial_fderiv (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun z : P × E ↦ fderiv ℝ (f z.1) z.2) := by
  have h : ContDiff ℝ ∞ (fun z : (P × E) × E ↦ f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv contDiff_snd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_QuadraticFamily
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma rawQuadratic_smooth :
    ContDiff ℝ ∞ (Function.uncurry (rawQuadratic (E := E))) := by
  exact (contDiff_fst.fst.add (contDiff_fst.snd.fst.clm_apply contDiff_snd)).sub
    ((contDiff_fst.snd.snd.clm_apply contDiff_snd).clm_apply contDiff_snd |>.const_smul (1/2:ℝ))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AdaptedChartFamilyLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Filter
open scoped ContDiff Topology
open Yau.Jets
attribute [local instance] clmTopology clmAdd clmModule

variable {T : Type*} [TopologicalSpace T]

lemma actualFrameConnection_continuous (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap)) :
    Continuous (fun t ↦ actualFrameConnection g (y t) (e t)) :=
  frameConnection_continuous _ _ ((smooth_metric_connection_continuous g hg hp).comp hy) he

end

open Set Filter
open scoped ContDiff Topology
variable {T E F : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E]
  [TopologicalSpace F]

variable [NormedSpace ℝ E] [CompleteSpace E]

theorem compact_quadratic_chart_domain {s : Set T} (hs : IsCompact s)
    (y : T → E) (hy : Continuous y)
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → E →L[ℝ] E →L[ℝ] E) (hB : Continuous B)
    {U : Set E} (hU : IsOpen U) (hyU : ∀ t ∈ s, y t ∈ U) :
    ∃ r > 0, ∀ t ∈ s, ∀ x : E, ‖x‖ < r →
      quadraticChartMap (y t) (e t) (B t) x ∈ U ∧
      ∃ J : E ≃L[ℝ] E, J.toContinuousLinearMap =
        fderiv ℝ (quadraticChartMap (y t) (e t) (B t)) x := by
  have hF : Continuous (fun z : T × E ↦ quadraticChartMap (y z.1) (e z.1) (B z.1) z.2) :=
    rawQuadratic_smooth.continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  have hJ : Continuous (fun z : T × E ↦ fderiv ℝ
      (quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  obtain ⟨r,hr,hri⟩ := compact_family_common_radius hs _ hF hU
    (fun t ht ↦ by simpa [quadraticChartMap_zero] using hyU t ht)
  obtain ⟨d,hd,hdj⟩ := compact_family_common_radius hs _ hJ ContinuousLinearEquiv.isOpen
    (fun t _ ↦ ⟨e t, (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv.symm⟩)
  refine ⟨min r d, lt_min hr hd, ?_⟩
  intro t ht x hx
  exact ⟨hri t ht x (lt_of_lt_of_le hx (min_le_left _ _)),
    hdj t ht x (lt_of_lt_of_le hx (min_le_right _ _))⟩

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CommonInjectiveChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Filter Metric
open scoped ContDiff Topology NNReal
noncomputable section
variable {T E : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Nontrivial E]

omit [Nontrivial E] in
lemma frame_inverse_continuous (e : T → E ≃L[ℝ] E)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap)) :
    Continuous (fun t ↦ (e t).symm.toContinuousLinearMap) := by
  have hi : Continuous (fun t ↦ ContinuousLinearMap.inverse (e t).toContinuousLinearMap) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hi : ContinuousAt (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
        (e t).toContinuousLinearMap :=
      (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (e t)).continuousAt
    exact ContinuousAt.comp (x := t) (g := ContinuousLinearMap.inverse)
      (f := fun t ↦ (e t).toContinuousLinearMap) hi he.continuousAt
  simpa only [ContinuousLinearMap.inverse_equiv] using hi

omit [CompleteSpace E] [Nontrivial E] in
lemma approximates_of_derivative_bound (f : E → E) (hf : ContDiff ℝ ∞ f)
    (e : E ≃L[ℝ] E) (r : ℝ) (c : ℝ≥0)
    (hD : ∀ x ∈ Metric.ball (0:E) r, ‖fderiv ℝ f x - e.toContinuousLinearMap‖ ≤ c) :
    ApproximatesLinearOn f e.toContinuousLinearMap (Metric.ball 0 r) c := by
  apply LipschitzOnWith.approximatesLinearOn
  apply (convex_ball (0:E) r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x _
    exact (hf.differentiable (by simp) x).sub e.differentiableAt
  · intro x hx
    rw [((hf.differentiable (by simp) x).hasFDerivAt.sub e.toContinuousLinearMap.hasFDerivAt).fderiv]
    exact hD x hx

theorem compact_common_chart
    {s : Set T} (hs : IsCompact s) (f : T → E → E)
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hD : Continuous (fun z : T × E ↦ fderiv ℝ (f z.1) z.2))
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (h0 : ∀ t, fderiv ℝ (f t) 0 = (e t).toContinuousLinearMap)
    (R : ℝ) (hR : 0 < R) :
    ∃ r > 0, r ≤ R ∧ ∃ d > 0, ∀ t ∈ s, ∃ F : OpenPartialHomeomorph E E,
      (F : E → E) = f t ∧ F.source = Metric.ball 0 r ∧
      Metric.closedBall (f t 0) d ⊆ F.target := by
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuousOn (frame_inverse_continuous e he).continuousOn
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let c : ℝ≥0 := ⟨1 / (2*M), by positivity⟩
  have hcpos : 0 < (c:ℝ) := by change 0 < 1 / (2*M); positivity
  have hMc : M * (c:ℝ) = 1/2 := by change M * (1 / (2*M)) = 1/2; field_simp
  have hsmall (t : T) (ht : t ∈ s) : c < ‖(e t).symm.toContinuousLinearMap‖₊⁻¹ := by
    have hn := (e t).symm.norm_pos
    have hb : ‖(e t).symm.toContinuousLinearMap‖ ≤ M := (hC t ht).trans (le_max_left _ _)
    change (c:ℝ) < ‖(e t).symm.toContinuousLinearMap‖⁻¹
    rw [← one_div]
    apply (lt_div_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_right hb hcpos.le]
  have hcGap (t : T) (ht : t ∈ s) :
      (c:ℝ) ≤ ‖(e t).symm.toContinuousLinearMap‖⁻¹ - (c:ℝ) := by
    have hn := (e t).symm.norm_pos
    have hb : ‖(e t).symm.toContinuousLinearMap‖ ≤ M := (hC t ht).trans (le_max_left _ _)
    have hh : 2*(c:ℝ) ≤ ‖(e t).symm.toContinuousLinearMap‖⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hn).mpr
      nlinarith [mul_le_mul_of_nonneg_right hb hcpos.le]
    linarith
  obtain ⟨r0,hr0,hr0i⟩ := compact_family_common_radius hs
    (fun z : T × E ↦ fderiv ℝ (f z.1) z.2 - (e z.1).toContinuousLinearMap)
    (hD.sub (he.comp continuous_fst)) (isOpen_ball (x := (0 : E →L[ℝ] E)) (ε := (c:ℝ)))
    (fun t _ ↦ by simpa [h0, Metric.mem_ball] using hcpos)
  let r := min r0 R
  have hr : 0 < r := lt_min hr0 hR
  have hri (t : T) (ht : t ∈ s) (x : E) (hx : ‖x‖ < r) :=
    hr0i t ht x (lt_of_lt_of_le hx (min_le_left _ _))
  refine ⟨r,hr,min_le_right _ _,(c:ℝ)*(r/2),mul_pos hcpos (by linarith),?_⟩
  intro t ht
  have happ := approximates_of_derivative_bound (f t) (hf t) (e t) r c (fun x hx ↦ by
    have hh := hri t ht x (by simpa using hx)
    exact le_of_lt (by simpa using hh))
  let F := happ.toOpenPartialHomeomorph (f t) (Metric.ball 0 r) (Or.inr (hsmall t ht)) isOpen_ball
  refine ⟨F,rfl,rfl,?_⟩
  apply Set.Subset.trans (Metric.closedBall_subset_closedBall ?_)
    (happ.closedBall_subset_target (Or.inr (hsmall t ht)) isOpen_ball
      (show 0 ≤ r/2 by linarith) (Metric.closedBall_subset_ball (by linarith)))
  exact mul_le_mul_of_nonneg_right (hcGap t ht) (by linarith)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartPushforward
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma chartPushforward_eventually (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (z : _root_.OAI.Yau.Jets.Coord) (hz : z ∈ F.target) :
    chartPushforward F u =ᶠ[𝓝 z] u ∘ F.symm := by
  filter_upwards [F.open_target.mem_nhds hz] with w hw
  simp [chartPushforward,hw]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartDerivativeTransfer
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma chart_comp_derivative_bound (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (hF : ContDiffOn ℝ ∞ F.symm F.target) (u : _root_.OAI.Yau.Jets.Coord → ℂ)
    (hu : ContDiffOn ℝ ∞ u F.source) (z : _root_.OAI.Yau.Jets.Coord) (hz : z ∈ F.target)
    (k : ℕ) (C D : ℝ)
    (hC : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i u (F.symm z)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i (F.symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) z‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ k (u ∘ F.symm) z‖ ≤ k.factorial * C * D^k := by
  have h := norm_iteratedFDerivWithin_comp_le hu hF (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))
    F.open_source.uniqueDiffOn F.open_target.uniqueDiffOn (fun _ hx ↦ F.map_target hx) hz
    (C := C) (D := D)
  simp only [iteratedFDerivWithin_of_isOpen _ F.open_source (F.map_target hz),
    iteratedFDerivWithin_of_isOpen _ F.open_target hz] at h
  exact h hC hD

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalSpatialJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma smooth_spatial_fderiv_at (f : P → E → F) (p : P) (x : E)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (p,x)) :
    ContDiffAt ℝ ∞ (fun z : P × E ↦ fderiv ℝ (f z.1) z.2) (p,x) := by
  have h : ContDiffAt ℝ ∞ (fun z : (P × E) × E ↦ f z.1.1 z.2) ((p,x),x) := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      (ContDiffAt.comp (g := Function.uncurry f)
        (f := fun z : (P × E) × E ↦ (z.1.1,z.2)) ((p,x),x) hf
        (contDiffAt_fst.fst.prodMk contDiffAt_snd))
  exact h.fderiv contDiffAt_snd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_InverseChartJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem inverseSpatialJet_smooth_at (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (k : ℕ) : ContDiffAt ℝ ∞ (fun z : QuadParam _root_.OAI.Yau.Jets.Coord × _root_.OAI.Yau.Jets.Coord ↦ inverseSpatialJet z.1 k z.2) (p,x) := by
  induction k with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord).symm.contDiff.contDiffAt.comp
      (p,x) contDiffAt_snd
  | succ k ih =>
    have hi : ContDiffAt ℝ ∞
        (fun z : QuadParam _root_.OAI.Yau.Jets.Coord × _root_.OAI.Yau.Jets.Coord ↦ ContinuousLinearMap.inverse (fderiv ℝ (rawQuadratic z.1) z.2)) (p,x) := by
      have h := contDiffAt_map_inverse (n := ∞) J
      rw [← hJ] at h
      exact h.comp (p,x) (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).contDiffAt
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ _root_.OAI.Yau.Jets.Coord) _root_.OAI.Yau.Jets.Coord).symm.contDiff.contDiffAt.comp
      (p,x) ((smooth_spatial_fderiv_at (fun p x ↦ inverseSpatialJet p k x) p x ih).clm_comp hi)

theorem inverseSpatialJet_eq (p : QuadParam _root_.OAI.Yau.Jets.Coord)
    (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord) (hF : (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = rawQuadratic p)
    (hInv : ContDiffOn ℝ ∞ F.symm F.target)
    (hJ : ∀ x ∈ F.source, ∃ J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (k : ℕ) (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ F.source) :
    inverseSpatialJet p k x = iteratedFDeriv ℝ k (F.symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (F x) := by
  induction k generalizing x with
  | zero =>
    simp only [inverseSpatialJet,iteratedFDeriv_zero_eq_comp,Function.comp_def,F.left_inv hx]
  | succ k ih =>
    obtain ⟨J,hJe⟩ := hJ x hx
    have hfd : DifferentiableAt ℝ (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) x := by
      rw [hF]
      exact (rawQuadratic_smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
    have hId : DifferentiableAt ℝ (iteratedFDeriv ℝ k (F.symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord)) (F x) :=
      (hInv.contDiffAt (F.open_target.mem_nhds (F.map_source hx))).differentiableAt_iteratedFDeriv
        (by exact_mod_cast (show (k : ℕ∞) < ⊤ by simp))
    have he : inverseSpatialJet p k =ᶠ[𝓝 x]
        (iteratedFDeriv ℝ k (F.symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord)) ∘ F := by
      filter_upwards [F.open_source.mem_nhds hx] with z hz
      exact ih z hz
    have hd : fderiv ℝ (inverseSpatialJet p k) x =
        fderiv ℝ ((iteratedFDeriv ℝ k (F.symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord)) ∘ F) x := he.fderiv_eq
    rw [fderiv_comp x hId hfd] at hd
    have hFder : fderiv ℝ (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) x = J.toContinuousLinearMap := by rw [hF,hJe]
    rw [hFder] at hd
    simp only [inverseSpatialJet,hd,hJe,ContinuousLinearMap.inverse_equiv]
    rw [ContinuousLinearMap.comp_assoc]
    have hcancel : J.toContinuousLinearMap.comp J.symm.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ _root_.OAI.Yau.Jets.Coord := by ext v; simp
    rw [hcancel,ContinuousLinearMap.comp_id]
    rfl

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_UniformInverseChartBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem compact_inverse_derivative_bounds {s : Set T} (hs : IsCompact s)
    (p : T → QuadParam _root_.OAI.Yau.Jets.Coord) (hp : Continuous p)
    (F : T → OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (hF : ∀ t ∈ s, (F t : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = rawQuadratic (p t))
    (hInv : ∀ t ∈ s, ContDiffOn ℝ ∞ (F t).symm (F t).target)
    (hJ : ∀ t ∈ s, ∀ x ∈ (F t).source, ∃ J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      fderiv ℝ (rawQuadratic (p t)) x = J.toContinuousLinearMap)
    (R : ℝ) (hR : ∀ t ∈ s, closedBall (0:_root_.OAI.Yau.Jets.Coord) R ⊆ (F t).source) (k0 : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ t ∈ s, ∀ x ∈ closedBall (0:_root_.OAI.Yau.Jets.Coord) R,
      ∀ k : ℕ, 1 ≤ k → k ≤ k0 →
        ‖iteratedFDeriv ℝ k ((F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (F t x)‖ ≤ D^k := by
  have hcont (k : ℕ) : ContinuousOn
      (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ inverseSpatialJet (p z.1) k z.2) (s ×ˢ closedBall 0 R) := by
    intro z hz
    obtain ⟨J,hJe⟩ := hJ z.1 hz.1 z.2 (hR z.1 hz.1 hz.2)
    exact (ContinuousAt.comp (x := z)
      (g := fun q : QuadParam _root_.OAI.Yau.Jets.Coord × _root_.OAI.Yau.Jets.Coord ↦ inverseSpatialJet q.1 k q.2)
      (f := fun q : T × _root_.OAI.Yau.Jets.Coord ↦ (p q.1,q.2))
      (inverseSpatialJet_smooth_at (p z.1) z.2 J hJe k).continuousAt
      ((hp.comp continuous_fst).prodMk continuous_snd).continuousAt).continuousWithinAt
  have hbound (k : Fin (k0+1)) : ∃ C : ℝ, ∀ t ∈ s, ∀ x ∈ closedBall (0:_root_.OAI.Yau.Jets.Coord) R,
      ‖iteratedFDeriv ℝ k.val ((F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (F t x)‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hs.prod (isCompact_closedBall (0:_root_.OAI.Yau.Jets.Coord) R)).exists_bound_of_continuousOn (hcont k.val)
    refine ⟨C,?_⟩
    intro t ht x hx
    rw [← inverseSpatialJet_eq (p t) (F t) (hF t ht) (hInv t ht) (hJ t ht) k.val x (hR t ht hx)]
    exact hC (t,x) ⟨ht,hx⟩
  choose C hC using hbound
  let D : ℝ := max 1 (∑ k, |C k|)
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨D,hD,?_⟩
  intro t ht x hx k hk hk0
  let i : Fin (k0+1) := ⟨k,by omega⟩
  have hi : C i ≤ D := (le_abs_self _).trans
    ((Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i)).trans (le_max_right _ _))
  exact (hC i t ht x hx).trans (hi.trans (by simpa using pow_le_pow_right₀ hD hk))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_NestedChartBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma nested_chart_inverse (F H : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (he : (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = H) (hs : H.source ⊆ F.source)
    {z : _root_.OAI.Yau.Jets.Coord} (hz : z ∈ H.target) : F.symm z = H.symm z := by
  have hx := hs (H.map_target hz)
  have hv : F (H.symm z) = z := by rw [he]; exact H.right_inv hz
  calc
    F.symm z = F.symm (F (H.symm z)) := congrArg F.symm hv.symm
    _ = H.symm z := F.left_inv hx

lemma nested_chart_target (F H : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (he : (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = H) (hs : H.source ⊆ F.source) : H.target ⊆ F.target := by
  intro z hz
  have h := F.map_source (hs (H.map_target hz))
  rwa [he,H.right_inv hz] at h

lemma nested_chart_inverse_germ (F H : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (he : (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = H) (hs : H.source ⊆ F.source)
    {z : _root_.OAI.Yau.Jets.Coord} (hz : z ∈ H.target) :
    (F.symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) =ᶠ[𝓝 z] H.symm := by
  filter_upwards [H.open_target.mem_nhds hz] with x hx
  exact nested_chart_inverse F H he hs hx

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem existing_chart_target_bounds
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y)
    (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord) (hB : Continuous B)
    (F : T → OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (hF : ∀ t, (F t : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = quadraticChartMap (y t) (e t) (B t))
    (r : ℝ) (hr : 0 < r) (hsource : ∀ t, (F t).source = ball 0 r)
    (k0 : ℕ) :
    ∃ delta > 0, ∃ R > 0, ∃ D : ℝ, 1 ≤ D ∧ ∀ t z,
      ‖z-y t‖ ≤ delta → z ∈ (F t).target ∧ ‖(F t).symm z‖ ≤ R ∧
      ContDiffAt ℝ ∞ ((F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) z ∧
      ∀ k, 1 ≤ k → k ≤ k0 → ‖iteratedFDeriv ℝ k ((F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) z‖ ≤ D^k := by
  let p : T → QuadParam _root_.OAI.Yau.Jets.Coord := fun t ↦ (y t,(e t).toContinuousLinearMap,B t)
  have hp : Continuous p := hy.prodMk (he.prodMk hB)
  have hD : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ fderiv ℝ (rawQuadratic (p z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      ((hp.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨R0,hR0,hJ0⟩ := compact_quadratic_chart_domain isCompact_univ y hy e he B hB
    isOpen_univ (fun _ _ ↦ mem_univ _)
  obtain ⟨r1,hr1,hr1R,d1,hd1,hH⟩ := compact_common_chart isCompact_univ
    (fun t ↦ rawQuadratic (p t)) (fun t ↦ quadraticChartMap_smooth _ _ _) hD e he
    (fun t ↦ (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv)
    (min R0 r) (lt_min hR0 hr)
  choose H hHe hHs hHt using fun t ↦ hH t (mem_univ t)
  have hJF (t : T) (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ (H t).source) :
      ∃ J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord, fderiv ℝ (rawQuadratic (p t)) x = J.toContinuousLinearMap := by
    have hn : ‖x‖ < r1 := by simpa [hHs] using hx
    obtain ⟨J,hJ⟩ := (hJ0 t (mem_univ t) x
      (hn.trans_le (hr1R.trans (min_le_left _ _)))).2
    exact ⟨J,hJ.symm⟩
  have hIs (t : T) : ContDiffOn ℝ ∞ (H t).symm (H t).target := by
    intro z hz
    obtain ⟨J,hJ⟩ := hJF t _ ((H t).map_target hz)
    have hd : HasFDerivAt (H t : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) J.toContinuousLinearMap ((H t).symm z) := by
      rw [hHe,← hJ]
      exact (quadraticChartMap_smooth _ _ _).differentiable (by simp) _ |>.hasFDerivAt
    apply ((H t).contDiffAt_symm hz hd _).contDiffWithinAt
    rw [hHe]
    exact (quadraticChartMap_smooth _ _ _).contDiffAt
  obtain ⟨r2,hr2,hr2r,d2,hd2,hQ⟩ := compact_common_chart isCompact_univ
    (fun t ↦ rawQuadratic (p t)) (fun t ↦ quadraticChartMap_smooth _ _ _) hD e he
    (fun t ↦ (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv) (r1/2) (by positivity)
  choose Q hQe hQs hQt using fun t ↦ hQ t (mem_univ t)
  have hclosed (t : T) : closedBall (0:_root_.OAI.Yau.Jets.Coord) (r1/2) ⊆ (H t).source := by
    rw [hHs]; exact closedBall_subset_ball (by linarith)
  obtain ⟨D,hD1,hDb⟩ := compact_inverse_derivative_bounds isCompact_univ p hp H
    (fun t _ ↦ hHe t) (fun t _ ↦ hIs t) (fun t _ ↦ hJF t) (r1/2)
    (fun t _ ↦ hclosed t) k0
  have hHF (t : T) : (H t).source ⊆ (F t).source := by
    rw [hHs,hsource]; exact ball_subset_ball (hr1R.trans (min_le_right _ _))
  have hQH (t : T) : (Q t).source ⊆ (H t).source := by
    rw [hQs,hHs]; exact ball_subset_ball (by linarith)
  have hFH (t : T) : (F t : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = H t := (hF t).trans (hHe t).symm
  have hHQ (t : T) : (H t : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = Q t := (hHe t).trans (hQe t).symm
  refine ⟨d2,hd2,r1/2,by positivity,D,hD1,?_⟩
  intro t z hz
  have hzQ : z ∈ (Q t).target := hQt t (by simpa [rawQuadratic,mem_closedBall,dist_eq_norm] using hz)
  have hzH := nested_chart_target (H t) (Q t) (hHQ t) (hQH t) hzQ
  have hqnorm : ‖(Q t).symm z‖ ≤ r1/2 := by
    have h := (Q t).map_target hzQ
    rw [hQs,mem_ball,dist_zero_right] at h
    exact h.le.trans hr2r
  have hinv := nested_chart_inverse (F t) (H t) (hFH t) (hHF t) hzH
  have hinv2 := nested_chart_inverse (H t) (Q t) (hHQ t) (hQH t) hzQ
  have hEq := nested_chart_inverse_germ (F t) (H t) (hFH t) (hHF t) hzH
  have hn : (H t).symm z ∈ closedBall (0:_root_.OAI.Yau.Jets.Coord) (r1/2) := by
    simpa [mem_closedBall,hinv2] using hqnorm
  refine ⟨nested_chart_target (F t) (H t) (hFH t) (hHF t) hzH,
    by simpa [hinv,hinv2] using hqnorm,
    ((hIs t).contDiffAt ((H t).open_target.mem_nhds hzH)).congr_of_eventuallyEq hEq,?_⟩
  intro k hk hk0
  rw [(hEq.iteratedFDeriv ℝ k).self_of_nhds]
  have hb := hDb t (mem_univ t) ((H t).symm z) hn k hk hk0
  rwa [(H t).right_inv hzH] at hb

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformPolynomial
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T ι : Type*} [TopologicalSpace T] [Fintype ι]

omit [TopologicalSpace T] in
lemma polynomialFamily_contDiff (p : ι → CPoly) (c : T → ι → ℂ) (t : T) :
    ContDiff ℝ ∞ (polynomialFamily p c t) := by
  exact ContDiff.sum (fun i _ ↦ (reval_contDiff (p i)).const_smul (c t i))

omit [TopologicalSpace T] in
lemma polynomialFamily_iteratedFDeriv (p : ι → CPoly) (c : T → ι → ℂ) (t : T)
    (k : ℕ) (x : Coord) :
    iteratedFDeriv ℝ k (polynomialFamily p c t) x =
      ∑ i, c t i • iteratedFDeriv ℝ k (reval (p i)) x := by
  unfold polynomialFamily
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
    (((reval_contDiff (p i)).const_smul (c t i)).of_le
      (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  exact iteratedFDeriv_const_smul_apply'
    ((reval_contDiff (p i)).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt

theorem polynomialFamily_derivative_continuous (p : ι → CPoly) (c : T → ι → ℂ)
    (hc : ∀ i, Continuous (fun t ↦ c t i)) (k : ℕ) :
    Continuous (fun tx : T × Coord ↦ iteratedFDeriv ℝ k (polynomialFamily p c tx.1) tx.2) := by
  simp_rw [polynomialFamily_iteratedFDeriv]
  apply continuous_finsetSum
  intro i _
  exact ((hc i).comp continuous_fst).smul
    (((reval_contDiff (p i)).continuous_iteratedFDeriv (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).comp continuous_snd)

theorem polynomialFamily_uniform_derivative_bound (p : ι → CPoly) (c : T → ι → ℂ)
    (hc : ∀ i, Continuous (fun t ↦ c t i)) (s : Set T) (hs : IsCompact s)
    (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (polynomialFamily p c t) x‖ ≤ C := by
  have hcompact := hs.prod (isCompact_closedBall (0 : Coord) R)
  have hbounded := (hcompact.image (polynomialFamily_derivative_continuous p c hc k)).isBounded
  obtain ⟨C, hC, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  apply hbound
  exact ⟨(t, x), ⟨ht, by simpa using hx⟩, rfl⟩

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ContinuousPolynomialFamily
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma polynomial_sum_of_support_subset (p : CPoly) (s : Finset (Fin 4 →₀ ℕ))
    (hs : p.support ⊆ s) : p = ∑ d ∈ s, p.coeff d • monomial d (1 : ℂ) := by
  simp only [smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [p.as_sum]
  exact Finset.sum_subset hs (fun d _ hd ↦ by simp [notMem_support_iff.mp hd])

lemma ContinuousPolyFamily.const (p : CPoly) : ContinuousPolyFamily (fun _ : T ↦ p) :=
  ⟨fun _ ↦ continuous_const, ⟨p.support, fun _ ↦ Finset.Subset.refl _⟩⟩

lemma ContinuousPolyFamily.add {P Q : T → CPoly}
    (hp : ContinuousPolyFamily P) (hq : ContinuousPolyFamily Q) :
    ContinuousPolyFamily (fun t ↦ P t + Q t) := by
  obtain ⟨s, hs⟩ := hp.2
  obtain ⟨r, hr⟩ := hq.2
  refine ⟨fun d ↦ by
    convert (hp.1 d).add (hq.1 d) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    simp, s ∪ r, ?_⟩
  intro t d hd
  have h := support_add hd
  rcases Finset.mem_union.mp h with h | h
  · exact Finset.mem_union_left _ (hs t h)
  · exact Finset.mem_union_right _ (hr t h)

lemma ContinuousPolyFamily.smul {P : T → CPoly} (hp : ContinuousPolyFamily P)
    {c : T → ℂ} (hc : Continuous c) : ContinuousPolyFamily (fun t ↦ c t • P t) := by
  obtain ⟨s, hs⟩ := hp.2
  refine ⟨fun d ↦ by
    convert hc.mul (hp.1 d) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    rw [coeff_smul]
    rfl, s, ?_⟩
  intro t d hd
  apply hs t
  rw [mem_support_iff] at hd ⊢
  simp only [coeff_smul, smul_eq_mul] at hd
  exact right_ne_zero_of_mul hd

lemma ContinuousPolyFamily.sum {ι : Type*} (s : Finset ι) {P : ι → T → CPoly}
    (hp : ∀ i ∈ s, ContinuousPolyFamily (P i)) :
    ContinuousPolyFamily (fun t ↦ ∑ i ∈ s, P i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (ContinuousPolyFamily.const (T := T) 0)
  | @insert i s hi ih =>
    simpa [Finset.sum_insert, hi] using (hp i (by simp)).add
      (ih (fun j hj ↦ hp j (by simp [hj])))

theorem ContinuousPolyFamily.uniform_derivative_bound {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (s : Set T) (hs : IsCompact s) (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (reval (P t)) x‖ ≤ C := by
  obtain ⟨r, hr⟩ := hp.2
  have he (t : T) : reval (P t) = polynomialFamily
      (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val) t := by
    funext x
    rw [polynomial_sum_of_support_subset (P t) r (hr t)]
    simp [polynomialFamily, reval, Algebra.smul_def]
    exact (Finset.sum_attach r (fun d ↦ (P t).coeff d *
      eval (fun i ↦ (x i : ℂ)) (monomial d (1 : ℂ)))).symm
  obtain ⟨C, hC, hb⟩ := polynomialFamily_uniform_derivative_bound
    (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val)
    (fun d ↦ hp.1 d.val) s hs R k
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  rw [he t]
  exact hb t ht x hx

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteAmplitude
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma finiteAmplitude_contDiff (A : ℕ → CPoly) (J : ℕ) (N : ℝ) :
    ContDiff ℝ ∞ (finiteAmplitude A J N) := polynomialFamily_contDiff _ _ _

lemma reval_center (p : CPoly) : reval p 0 = p.coeff 0 := by
  simp [reval, MvPolynomial.constantCoeff_eq]

theorem finiteAmplitude_center (A : ℕ → CPoly) (J : ℕ) (N : ℝ)
    (hA : ∀ j, MvPolynomial.homogeneousComponent 0 (A j) = if j = 0 then 1 else 0) :
    finiteAmplitude A J N 0 = 1 := by
  have hc (j : ℕ) : reval (A j) 0 = if j = 0 then 1 else 0 := by
    have h := congrArg (fun polynomial : CPoly ↦ polynomial.coeff 0) (hA j)
    by_cases hj : j = 0 <;>
      simpa [reval_center, MvPolynomial.coeff_homogeneousComponent, hj] using h
  simp [finiteAmplitude, polynomialFamily, hc, smul_eq_mul, apply_ite]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformTransportPolynomial
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma ContinuousPolyFamily.comp {S : Type*} [TopologicalSpace S]
    {P : T → CPoly} (hp : ContinuousPolyFamily P) {f : S → T} (hf : Continuous f) :
    ContinuousPolyFamily (fun s ↦ P (f s)) := by
  obtain ⟨r, hr⟩ := hp.2
  exact ⟨fun d ↦ (hp.1 d).comp hf, r, fun s ↦ hr (f s)⟩

lemma finiteAmplitude_reval (A : ℕ → CPoly) (J : ℕ) (N : ℝ) :
    finiteAmplitude A J N = reval (∑ j : Fin (J + 1), ((N⁻¹ : ℝ) : ℂ)^j.val • A j.val) := by
  funext x
  simp [finiteAmplitude, polynomialFamily, reval, Algebra.smul_def]

theorem finiteAmplitude_parameter_uniform_derivative_bound
    (A : ℕ → T → CPoly) (hA : ∀ j, ContinuousPolyFamily (A j))
    (J k : ℕ) (s : Set T) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (finiteAmplitude (fun j ↦ A j t) J N) x‖ ≤ C := by
  let P : T × ℝ → CPoly := fun z ↦
    ∑ j : Fin (J + 1), (z.2 : ℂ)^j.val • A j.val z.1
  have hP : ContinuousPolyFamily P := by
    apply ContinuousPolyFamily.sum
    intro j _
    exact ((hA j.val).comp continuous_fst).smul
      ((Complex.continuous_ofReal.comp continuous_snd).pow j.val)
  obtain ⟨C, hC, hb⟩ := hP.uniform_derivative_bound
    (s ×ˢ Set.Icc (0 : ℝ) 1) (hs.prod isCompact_Icc) R k
  refine ⟨C, hC, ?_⟩
  intro t ht N hN x hx
  rw [finiteAmplitude_reval]
  exact hb (t, N⁻¹) ⟨ht, inv_nonneg.mpr (le_trans zero_le_one hN), inv_le_one_of_one_le₀ hN⟩ x hx

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Waves
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E]

lemma scaledCutoff_eq_one {N : ℝ} (hN : 0 < N) (y x : E)
    (hx : ‖x - y‖ ≤ N ^ (-1 / 3 : ℝ)) : scaledCutoff N y x = 1 := by
  apply (baseCutoff (E := E)).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hN _)]
  change N ^ (1 / 3 : ℝ) * ‖x - y‖ ≤ 1
  calc
    _ ≤ N ^ (1 / 3 : ℝ) * N ^ (-1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hN.le _)
    _ = 1 := by rw [← Real.rpow_add hN]; norm_num

end
end Yau.Waves

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformSmoothBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

variable {T : Type*} [TopologicalSpace T]

theorem compact_smooth_derivative_bound (f : T → Coord → ℂ) (k : ℕ)
    (hc : ∀ j, j ≤ k → Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ j (f z.1) z.2))
    (s : Set T) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R → DerivativeBound k (f t) x C := by
  have hb (j : Fin (k+1)) : ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ j.val (f t) x‖ ≤ C := by
    obtain ⟨C, hC, h⟩ := ((hs.prod (isCompact_closedBall (0 : Coord) R)).image
      (hc j.val (by omega))).isBounded.exists_pos_norm_le
    refine ⟨C, hC, fun t ht x hx ↦ h _ ?_⟩
    exact ⟨(t,x), ⟨ht, by simpa using hx⟩, rfl⟩
  choose C hC h using hb
  refine ⟨∑ j, C j, ?_, ?_⟩
  · exact (hC ⟨0, by omega⟩).trans_le (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))
  · intro t ht x hx j hj
    exact (h ⟨j, by omega⟩ t ht x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothDefectBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma uniformSmoothBounded_of_continuous_derivatives (s : Set T) (hs : IsCompact s)
    (R : ℝ) (f : T → Coord → ℂ) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hc : ∀ j, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ j (f z.1) z.2)) :
    UniformSmoothBounded s R f :=
  ⟨hf, fun k ↦ compact_smooth_derivative_bound f k (fun j _ ↦ hc j) s hs R⟩

lemma ContinuousPolyFamily.derivative_continuous {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (k : ℕ) :
    Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (reval (P z.1)) z.2) := by
  obtain ⟨r, hr⟩ := hp.2
  have he (t : T) : reval (P t) = polynomialFamily
      (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val) t := by
    funext x
    rw [polynomial_sum_of_support_subset (P t) r (hr t)]
    simp [polynomialFamily, reval, Algebra.smul_def]
    exact (Finset.sum_attach r (fun d ↦ (P t).coeff d *
      eval (fun i ↦ (x i : ℂ)) (monomial d (1 : ℂ)))).symm
  simp_rw [he]
  exact polynomialFamily_derivative_continuous
    (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val)
    (fun d ↦ hp.1 d.val) k

lemma ContinuousPolyFamily.uniformSmoothBounded {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (s : Set T) (hs : IsCompact s) (R : ℝ) :
    UniformSmoothBounded s R (fun t ↦ reval (P t)) := by
  apply uniformSmoothBounded_of_continuous_derivatives s hs R _ (fun t ↦ reval_contDiff _)
  exact hp.derivative_continuous

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_UniformUncutResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma finiteAmplitude_all_parameter_derivatives (A : ℕ → T → CPoly)
    (hA : ∀ j, ContinuousPolyFamily (A j)) (J k : ℕ)
    (s : Set T) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord, ‖x‖ ≤ R →
      DerivativeBound k (finiteAmplitude (fun j ↦ A j t) J N) x C := by
  have h (j : Fin (k+1)) := finiteAmplitude_parameter_uniform_derivative_bound A hA J j.val s hs R
  choose C hC hb using h
  refine ⟨∑ j, C j, ?_, ?_⟩
  · exact (hC ⟨0, by omega⟩).trans_le
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))
  · intro t ht N hN x hx j hj
    exact (hb ⟨j, by omega⟩ t ht N hN x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CommonLocalExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem common_local_smooth_extension {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (f : _root_.OAI.Yau.Jets.Coord → F) (hf : ContDiffOn ℝ ∞ f U) {y : _root_.OAI.Yau.Jets.Coord} (hy : y ∈ U) :
    ∃ (r : ℝ) (G : _root_.OAI.Yau.Jets.Coord → F), 0 < r ∧ ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ U ∧ Metric.closedBall y r ⊆ U ∧
      (∀ x ∈ Metric.ball y r, G x = f x) ∧
      ∀ x ∈ Metric.ball y r, G =ᶠ[𝓝 x] f := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
  let beta : ContDiffBump y := ⟨r/4, r/2, by positivity, by linarith⟩
  have hsupport : tsupport beta ⊆ U := by
    rw [beta.tsupport_eq]
    intro x hx
    apply hball
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    dsimp [beta] at hx'
    linarith
  let G := fun x ↦ beta x • f x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport beta
    · exact beta.contDiff.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsupport hx)))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      have hn : (tsupport beta)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
      filter_upwards [hn] with z hz
      simp [G, image_eq_zero_of_notMem_tsupport hz]
  have hsub : tsupport G ⊆ tsupport beta := by
    apply closure_mono
    intro x hx
    change beta x ≠ 0
    intro hz
    exact hx (by simp [G, hz])
  have heq : ∀ x ∈ Metric.ball y (r/4), G x = f x := by
    intro x hx
    have hb : beta x = 1 := beta.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [G, hb]
  refine ⟨r/4, G, by positivity, hG,
    beta.hasCompactSupport.of_isClosed_subset isClosed_closure hsub,
    hsub.trans hsupport, ?_, heq, ?_⟩
  · intro x hx
    apply hball
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    linarith
  · intro x hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact heq z hz

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma rescaling_radius_bound {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) :
    0 ≤ (N*s)⁻¹ ∧ (N*s)⁻¹ ≤ 1 ∧ N*(N*s)⁻¹ ≤ 1 := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  refine ⟨by positivity,(inv_le_one₀ (mul_pos hN0 hs0)).mpr
    (one_le_mul_of_one_le_of_one_le hN hs),?_⟩
  have he : N*(N*s)⁻¹ = s⁻¹ := by field_simp
  rw [he]
  exact (inv_le_one₀ hs0).mpr hs

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_TripleWaveParameters
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]
variable {g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {p : T → _root_.OAI.Yau.Jets.Coord}
namespace AdmissibleFrameTriple
variable (d : AdmissibleFrameTriple g H p)

lemma continuous_frame : Continuous (fun z ↦ (d.frame z).toContinuousLinearMap) := by
  apply continuous_prod_of_discrete_right.mpr
  intro j
  exact frameEquiv_continuous g (fun t ↦ d.e t j) (d.continuous_e j) (fun t ↦ d.orthonormal t j)

end AdmissibleFrameTriple

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveCenterJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

lemma zero_mem_source (t : T × Fin 3) : (0:_root_.OAI.Yau.Jets.Coord) ∈ (b.F t).source := by
  rw [(b.chart_domain t).1]
  simpa using b.sourceRadius_pos

lemma chart_zero (t : T × Fin 3) : b.F t 0 = y t.1 := by
  rw [b.chart_eq]
  exact quadraticChartMap_zero _ _ _

lemma inverse_center (t : T × Fin 3) : (b.F t).symm (y t.1) = 0 := by
  rw [← b.chart_zero t]
  exact (b.F t).left_inv (b.zero_mem_source t)

lemma amplitude_center (N : ℝ) (t : T × Fin 3) : b.amplitude N t (y t.1) = 1 := by
  unfold amplitude
  simp only [Function.comp_apply,b.inverse_center]
  exact finiteAmplitude_center _ _ _ (fun j ↦ b.jets.amplitude_value j t)

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_spatial_bounds (hg : ContDiff ℝ ∞ g)
    (hpos : ∀ x v, v ≠ 0 → 0 < g x v v) (hy : Continuous y) (k : ℕ) :
    ∃ delta > 0, ∃ C > 0, ∃ D : ℝ, 1 ≤ D ∧ ∀ t x,
      ‖x-y t.1‖ ≤ delta → x ∈ (b.F t).target ∧
      ContDiffAt ℝ ∞ (b.phase t) x ∧
      (∀ N, ContDiffAt ℝ ∞ (b.amplitude N t) x) ∧
      (∀ i, i ≤ k → ‖iteratedFDeriv ℝ i (b.phase t) x‖ ≤ C) ∧
      (∀ N, 1 ≤ N → ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i (b.amplitude N t) x‖ ≤ C) ∧
      ContDiffAt ℝ ∞ ((b.F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) x ∧
      ‖fderiv ℝ ((b.F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) x‖ ≤ D := by
  have hB := actualFrameConnection_continuous g hg hpos (fun t : T × Fin 3 ↦ y t.1)
    (hy.comp continuous_fst) d.frame d.continuous_frame
  obtain ⟨delta,hd,R,hR,D,hD,hbound⟩ := existing_chart_target_bounds
    (fun t : T × Fin 3 ↦ y t.1) (hy.comp continuous_fst) d.frame d.continuous_frame
    (fun t ↦ actualFrameConnection g (y t.1) (d.frame t)) hB b.F b.chart_eq
    b.sourceRadius b.sourceRadius_pos (fun t ↦ (b.chart_domain t).1) (max k 1)
  obtain ⟨Cp,hCp,hp⟩ := (b.jets.phase_continuous.uniformSmoothBounded univ isCompact_univ R).2 k
  obtain ⟨Ca,hCa,ha⟩ := finiteAmplitude_all_parameter_derivatives b.A
    b.jets.amplitude_continuous J k univ isCompact_univ R
  let C := (k.factorial:ℝ)*(Cp+Ca)*D^k
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨delta,hd,C,hC,D,hD,?_⟩
  intro t x hx
  obtain ⟨hxt,hxn,hxs,hxb⟩ := hbound t x hx
  have hpS : ContDiffAt ℝ ∞ (b.phase t) x := (reval_contDiff _).contDiffAt.comp x hxs
  have haS (N : ℝ) : ContDiffAt ℝ ∞ (b.amplitude N t) x :=
    (finiteAmplitude_contDiff _ _ _).contDiffAt.comp x hxs
  have hcost (i : ℕ) (hi : i ≤ k) : (i.factorial:ℝ)*(Cp+Ca)*D^i ≤ C := by
    have hf : (i.factorial:ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
    have hp := pow_le_pow_right₀ hD hi
    dsimp [C]
    gcongr
  refine ⟨hxt,hpS,haS,?_,?_,hxs,?_⟩
  · intro i hi
    have hb := chart_comp_derivative_bound (b.F t) (b.chart_domain t).2.2 (reval (b.phi t))
      (reval_contDiff _).contDiffOn x hxt i (Cp+Ca) D
      (fun j hj ↦ (hp t (mem_univ t) _ hxn j (hj.trans hi)).trans (by linarith))
      (fun j hj hji ↦ hxb j hj ((hji.trans hi).trans (le_max_left _ _)))
    exact hb.trans (hcost i hi)
  · intro N hN i hi
    have hb := chart_comp_derivative_bound (b.F t) (b.chart_domain t).2.2
      (finiteAmplitude (fun j ↦ b.A j t) J N) (finiteAmplitude_contDiff _ _ _).contDiffOn
      x hxt i (Cp+Ca) D
      (fun j hj ↦ (ha t (mem_univ t) N hN _ hxn j (hj.trans hi)).trans (by linarith))
      (fun j hj hji ↦ hxb j hj ((hji.trans hi).trans (le_max_left _ _)))
    exact hb.trans (hcost i hi)
  · simpa only [norm_iteratedFDeriv_one,pow_one] using hxb 1 le_rfl (le_max_right _ _)

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AmplitudeBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma norm_sub_le_on_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : _root_.OAI.Yau.Jets.Coord → E) (y : _root_.OAI.Yau.Jets.Coord) (r C : ℝ) (hC : 0 ≤ C)
    (hs : ∀ z, ‖z-y‖ ≤ r → DifferentiableAt ℝ f z)
    (hb : ∀ z, ‖z-y‖ ≤ r → ‖fderiv ℝ f z‖ ≤ C)
    (hr : 0 ≤ r) (x : _root_.OAI.Yau.Jets.Coord) (hx : ‖x-y‖ ≤ r) : ‖f x-f y‖ ≤ C*‖x-y‖ := by
  let c : NNReal := ⟨C,hC⟩
  have hl : LipschitzOnWith c f (closedBall y r) := by
    apply (convex_closedBall y r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro z hz; exact hs z (by simpa [mem_closedBall,dist_eq_norm] using hz)
    · intro z hz; exact hb z (by simpa [mem_closedBall,dist_eq_norm] using hz)
  have h := hl.dist_le_mul x
    (by simpa [mem_closedBall,dist_eq_norm] using hx) y (by simpa using hr)
  change dist (f x) (f y) ≤ C*dist x y at h
  simpa only [dist_eq_norm] using h

lemma complex_ne_zero_of_near_one (a : ℂ) (h : ‖a-1‖ ≤ (1/2:ℝ)) :
    (1/2:ℝ) ≤ ‖a‖ ∧ ‖a‖ ≤ 3/2 ∧ a ≠ 0 := by
  have hl := norm_add_le (1-a) a
  have hu := norm_add_le (a-1) (1:ℂ)
  rw [norm_sub_rev] at hl
  norm_num at hl hu
  constructor
  · linarith
  constructor
  · linarith
  · intro hz; simp [hz] at h; norm_num at h

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_amplitude_bounds (hg : ContDiff ℝ ∞ g)
    (hpos : ∀ x v, v ≠ 0 → 0 < g x v v) (hy : Continuous y) :
    ∃ delta > 0, ∃ C > 0, ∃ D : ℝ, 1 ≤ D ∧ ∀ t x,
      ‖x-y t.1‖ ≤ delta → x ∈ (b.F t).target ∧
      ‖(b.F t).symm x‖ ≤ D*‖x-y t.1‖ ∧
      ContDiffAt ℝ ∞ ((b.F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) x ∧
      ∀ N, 1 ≤ N → ContDiffAt ℝ ∞ (b.amplitude N t) x ∧
        ‖b.amplitude N t x-1‖ ≤ C*‖x-y t.1‖ ∧
        (1/2:ℝ) ≤ ‖b.amplitude N t x‖ ∧ ‖b.amplitude N t x‖ ≤ 3/2 ∧
        b.amplitude N t x ≠ 0 ∧ ‖fderiv ℝ (b.amplitude N t) x‖ ≤ C := by
  obtain ⟨delta,hd,C,hC,D,hD,hb⟩ := b.uniform_spatial_bounds hg hpos hy 1
  let r := min delta (1/(2*C))
  have hr : 0 < r := lt_min hd (by positivity)
  have hh (t : T × Fin 3) (x : _root_.OAI.Yau.Jets.Coord) (hx : ‖x-y t.1‖ ≤ r) :=
    hb t x (hx.trans (min_le_left _ _))
  refine ⟨r,hr,C,hC,D,hD,?_⟩
  intro t x hx
  have h := hh t x hx
  have hInv := norm_sub_le_on_closedBall ((b.F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (y t.1) r D
    (by linarith) (fun z hz ↦ (hh t z hz).2.2.2.2.2.1.differentiableAt (by simp))
    (fun z hz ↦ (hh t z hz).2.2.2.2.2.2) hr.le x hx
  rw [b.inverse_center,sub_zero] at hInv
  refine ⟨h.1,hInv,h.2.2.2.2.2.1,?_⟩
  intro N hN
  have hAmpDer (z : _root_.OAI.Yau.Jets.Coord) (hz : ‖z-y t.1‖ ≤ r) : ‖fderiv ℝ (b.amplitude N t) z‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using (hh t z hz).2.2.2.2.1 N hN 1 le_rfl
  have hAmp := norm_sub_le_on_closedBall (b.amplitude N t) (y t.1) r C hC.le
    (fun z hz ↦ ((hh t z hz).2.2.1 N).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hAmpDer hr.le x hx
  rw [b.amplitude_center] at hAmp
  have hsmall : C*‖x-y t.1‖ ≤ 1/2 := by
    have he := hx.trans (min_le_right delta (1/(2*C)))
    have he' := (le_div_iff₀ (by positivity : 0 < 2*C)).mp he
    nlinarith
  obtain ⟨hl,hu,hn⟩ := complex_ne_zero_of_near_one _ (hAmp.trans hsmall)
  exact ⟨h.2.2.1 N,hAmp,hl,hu,hn,hAmpDer x hx⟩

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AffineRescalingJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma affine_rescaling_derivative_power (f : _root_.OAI.Yau.Jets.Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (x v : _root_.OAI.Yau.Jets.Coord) {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f (x+r • z)) v‖ ≤
      r^k*‖iteratedFDeriv ℝ k f (x+r • v)‖ := by
  let L : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord := r • ContinuousLinearMap.id ℝ _root_.OAI.Yau.Jets.Coord
  have hL : ‖L‖ ≤ r := by
    apply ContinuousLinearMap.opNorm_le_bound _ hr
    intro z
    change ‖r • z‖ ≤ r*‖z‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  change ‖iteratedFDeriv ℝ k ((fun z ↦ f (x+z)) ∘ L) v‖ ≤ _
  have htrans : ContDiff ℝ ∞ (fun z : _root_.OAI.Yau.Jets.Coord ↦ f (x+z)) := hf.comp (contDiff_const.add contDiff_id)
  rw [L.iteratedFDeriv_comp_right htrans v
    (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)),iteratedFDeriv_comp_add_left]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg L) hL k) (norm_nonneg _)).trans_eq (mul_comm _ _)

lemma smoothOn_global_germ {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (f : _root_.OAI.Yau.Jets.Coord → ℂ) (hf : ContDiffOn ℝ ∞ f U) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ U) :
    ∃ F : _root_.OAI.Yau.Jets.Coord → ℂ, ContDiff ℝ ∞ F ∧ F =ᶠ[𝓝 x] f := by
  obtain ⟨r,F,hr,hF,_,_,_,_,he⟩ := common_local_smooth_extension hU f hf hx
  exact ⟨F,hF,he x (by simpa using hr)⟩

lemma affine_rescaling_derivative_power_on {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (f : _root_.OAI.Yau.Jets.Coord → ℂ) (hf : ContDiffOn ℝ ∞ f U) (x v : _root_.OAI.Yau.Jets.Coord)
    {r : ℝ} (hr : 0 ≤ r) (hz : x+r • v ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f (x+r • z)) v‖ ≤
      r^k*‖iteratedFDeriv ℝ k f (x+r • v)‖ := by
  obtain ⟨F,hF,he⟩ := smoothOn_global_germ hU f hf hz
  have hc : Continuous (fun z : _root_.OAI.Yau.Jets.Coord ↦ x+r • z) := continuous_const.add (continuous_id.const_smul r)
  have hh := he.comp_tendsto hc.continuousAt
  change (fun z ↦ F (x+r • z)) =ᶠ[𝓝 v] (fun z ↦ f (x+r • z)) at hh
  rw [← (hh.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds,← (he.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
  exact affine_rescaling_derivative_power F hF x v hr k

lemma radius_high_power {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) {k : ℕ} (hk : 2 ≤ k) :
    N*((N*s)⁻¹)^k ≤ N⁻¹ := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  obtain ⟨hr0,hr1,hNr⟩ := rescaling_radius_bound hN hs
  have hrN : (N*s)⁻¹ ≤ N⁻¹ := (inv_le_inv₀ (mul_pos hN0 (lt_of_lt_of_le zero_lt_one hs)) hN0).mpr (by nlinarith)
  have hpow := pow_le_pow_of_le_one hr0 hr1 hk
  calc
    _ ≤ N*((N*s)⁻¹)^2 := mul_le_mul_of_nonneg_left hpow hN0.le
    _ ≤ N*(N⁻¹)^2 := by gcongr
    _ = N⁻¹ := by field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_HalfScaleLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Filter
open scoped Topology

lemma main_scale_eventually (L D delta : ℝ) (hd : 0 < delta) :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧ L*N^(-5/12:ℝ) ≤ delta ∧
      D*(L*N^(-5/12:ℝ)) < N^(-1/3:ℝ) := by
  have hsmall : Tendsto (fun N : ℝ ↦ L*N^(-5/12:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/12)).const_mul L
  have hcut : Tendsto (fun N : ℝ ↦ (D*L)*N^(-1/12:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/12)).const_mul (D*L)
  filter_upwards [eventually_ge_atTop (1:ℝ),hsmall.eventually (gt_mem_nhds hd),
    hcut.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with N hN hs hc
  refine ⟨hN,hs.le,?_⟩
  have hp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have he : N^(-5/12:ℝ) = N^(-1/12:ℝ)*N^(-1/3:ℝ) := by
    rw [← Real.rpow_add hp]; norm_num
  rw [he]
  have hh := mul_lt_mul_of_pos_right hc (Real.rpow_pos_of_pos hp (-1/3:ℝ))
  simpa [mul_assoc] using hh

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_Logarithm
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

variable {T : Type*} [TopologicalSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

lemma wave_germ_of_small_inverse (N : ℝ) (hN : 0 < N) (t : T × Fin 3)
    (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ (b.F t).target)
    (hsmall : ‖(b.F t).symm x‖ < N^(-1/3:ℝ)) :
    b.wave N t =ᶠ[𝓝 x]
      (fun z ↦ b.amplitude N t z * Complex.exp ((N:ℂ)*b.phase t z)) := by
  have hInv := ((b.chart_domain t).2.2.contDiffAt ((b.F t).open_target.mem_nhds hx)).continuousAt
  have hnear : ∀ᶠ z in 𝓝 x, ‖(b.F t).symm z‖ < N^(-1/3:ℝ) :=
    hInv.norm.eventually (gt_mem_nhds hsmall)
  filter_upwards [chartPushforward_eventually (b.F t) (coordinateWave b.phi b.A J N t) x hx,hnear] with z hz hs
  change chartPushforward (b.F t) (coordinateWave b.phi b.A J N t) z = _
  rw [hz]
  have hc := Yau.Waves.scaledCutoff_eq_one hN (0:_root_.OAI.Yau.Jets.Coord) ((b.F t).symm z) (by simpa using hs.le)
  change Yau.Waves.scaledCutoff N (0:_root_.OAI.Yau.Jets.Coord) ((b.F t).symm z) • _ = _
  rw [hc,one_smul]
  rfl

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ShiftedCenterDistance
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section

lemma rescaling_displacement_bound {N s R : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s)
    {x v : _root_.OAI.Yau.Jets.Coord} (hv : ‖v‖ ≤ R) :
    N*‖(x+(N*s)⁻¹ • v)-x‖ ≤ R := by
  obtain ⟨hr0,_,hNr⟩ := rescaling_radius_bound hN hs
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr0]
  calc
    _ = (N*(N*s)⁻¹)*‖v‖ := by ring
    _ ≤ 1*‖v‖ := mul_le_mul_of_nonneg_right hNr (norm_nonneg _)
    _ ≤ R := by simpa using hv

lemma main_radius_times_frequency {N : ℝ} (hN : 0 < N) :
    N*N^(-5/12:ℝ) = N^(7/12:ℝ) := by
  calc
    _ = N^(1:ℝ)*N^(-5/12:ℝ) := by rw [Real.rpow_one]
    _ = N^((1:ℝ)+(-5/12)) := (Real.rpow_add hN _ _).symm
    _ = _ := by norm_num

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeMainLogJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma eventually_shifted_main_distance (R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : ℝ), 1 ≤ s → ∀ (x y v : _root_.OAI.Yau.Jets.Coord), ‖v‖ ≤ R →
      sourceEuclideanNorm (x-y) ≤ (n:ℝ)^(-5/12:ℝ) →
      ‖x+((n:ℝ)*s)⁻¹ • v-y‖ ≤ 2*(n:ℝ)^(-5/12:ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ (n:ℝ)^(7/12:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 7/12)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop R),eventually_gt_atTop (0:ℕ)]
    with n hn hnpos
  intro s hs x y v hv hnear
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hd := rescaling_displacement_bound (x := x) hn1 hs hv
  rw [← main_radius_times_frequency hn0] at hn
  have hshift : ‖(x+((n:ℝ)*s)⁻¹ • v)-x‖ ≤ (n:ℝ)^(-5/12:ℝ) := by nlinarith
  have hxy := (norm_le_sourceEuclideanNorm _).trans hnear
  have he : x+((n:ℝ)*s)⁻¹ • v-y =
      (x+((n:ℝ)*s)⁻¹ • v-x)+(x-y) := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_NormalizedWaveRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma amplitude_ratio_near_one {a b : ℂ} {e : ℝ} (ha : (1/2:ℝ) ≤ ‖a‖)
    (hb : ‖b-a‖ ≤ e) : ‖b/a-1‖ ≤ 2*e := by
  have hane : a ≠ 0 := by intro h; simp [h] at ha; norm_num at ha
  rw [show b/a-1 = (b-a)/a by field_simp,norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖a‖)).mpr
  have he : 0 ≤ e := (norm_nonneg _).trans hb
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_MainAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_main_amplitude_ratio (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hy : Continuous y)
    (R e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ t x s, 1 ≤ s →
      sourceEuclideanNorm (x-y t.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R →
      b.amplitude n t x ≠ 0 ∧
      ‖b.amplitude n t (x+((n:ℝ)*s)⁻¹ • v)/b.amplitude n t x-1‖ ≤ e ∧
      (b.wave n t =ᶠ[𝓝 x] (fun z ↦ b.amplitude n t z*Complex.exp ((n:ℂ)*b.phase t z))) ∧
      (b.wave n t =ᶠ[𝓝 (x+((n:ℝ)*s)⁻¹ • v)]
        (fun z ↦ b.amplitude n t z*Complex.exp ((n:ℂ)*b.phase t z))) := by
  obtain ⟨delta,hd,C,hC,D,hD,hb⟩ := b.uniform_amplitude_bounds hg hp hy
  filter_upwards [eventually_shifted_main_distance R,
    eventually_nat_frequency (main_scale_eventually 2 D delta hd),
    eventually_nat_frequency (main_scale_eventually (6*C) 1 e he)] with n hshift hn heps
  intro t x s hs hnear v hv
  have hN0 : 0 < (n:ℝ) := lt_of_lt_of_le zero_lt_one hn.1
  have hr : 0 < (n:ℝ)^(-5/12:ℝ) := Real.rpow_pos_of_pos hN0 _
  have hx := (norm_le_sourceEuclideanNorm _).trans hnear
  have hz := hshift s hs x (y t.1) v hv hnear
  have hx2 : ‖x-y t.1‖ ≤ 2*(n:ℝ)^(-5/12:ℝ) := by linarith
  have hall (z : _root_.OAI.Yau.Jets.Coord) (hz : ‖z-y t.1‖ ≤ 2*(n:ℝ)^(-5/12:ℝ)) := hb t z (hz.trans hn.2.1)
  have hbx := hall x hx2
  have hbz := hall _ hz
  have hagx := hbx.2.2.2 n hn.1
  have hagz := hbz.2.2.2 n hn.1
  have hdiff : ‖b.amplitude n t (x+((n:ℝ)*s)⁻¹ • v)-b.amplitude n t x‖ ≤
      3*C*(n:ℝ)^(-5/12:ℝ) := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ 1 _).trans
    rw [norm_sub_rev (1:ℂ)]
    exact (add_le_add hagz.2.1 hagx.2.1).trans (by nlinarith)
  refine ⟨hagx.2.2.2.2.1,(amplitude_ratio_near_one hagx.2.2.1 hdiff).trans (by nlinarith [heps.2.1]),?_,?_⟩
  · exact b.wave_germ_of_small_inverse n hN0 t x hbx.1
      ((hbx.2.1.trans (mul_le_mul_of_nonneg_left hx2 (by linarith))).trans_lt hn.2.2)
  · exact b.wave_germ_of_small_inverse n hN0 t _ hbz.1
      ((hbz.2.1.trans (mul_le_mul_of_nonneg_left hz (by linarith))).trans_lt hn.2.2)

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledHigherJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma iteratedFDeriv_linear_high (L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ) (v : _root_.OAI.Yau.Jets.Coord) {k : ℕ} (hk : 2 ≤ k) :
    iteratedFDeriv ℝ k L v = 0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  apply norm_eq_zero.mp
  rw [show 2+j = (j+1)+1 by omega,← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ ↦ L := by funext z; exact L.fderiv
  rw [he,iteratedFDeriv_succ_const]
  simp

lemma rescaledPhaseDefect_smooth (phi : _root_.OAI.Yau.Jets.Coord → ℂ) (L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ)
    (N s : ℝ) (x v : _root_.OAI.Yau.Jets.Coord) (hp : ContDiffAt ℝ ∞ phi (x+(N*s)⁻¹ • v)) :
    ContDiffAt ℝ ∞ (rescaledPhaseDefect phi L N s x) v := by
  exact (contDiffAt_const.mul ((hp.comp v
    (contDiff_const.add (contDiff_id.const_smul _)).contDiffAt).sub contDiffAt_const)).sub
    (L.contDiff.contDiffAt.const_smul _)

lemma rescaledPhaseDefect_high_bound {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (phi : _root_.OAI.Yau.Jets.Coord → ℂ) (hp : ContDiffOn ℝ ∞ phi U) (L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ)
    {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) (x v : _root_.OAI.Yau.Jets.Coord)
    (hz : x+(N*s)⁻¹ • v ∈ U) {k : ℕ} (hk : 2 ≤ k) {C : ℝ}
    (hC : 0 ≤ C) (hb : ‖iteratedFDeriv ℝ k phi (x+(N*s)⁻¹ • v)‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (rescaledPhaseDefect phi L N s x) v‖ ≤ C/N := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hr := (rescaling_radius_bound hN hs).1
  let F : _root_.OAI.Yau.Jets.Coord → ℂ := fun z ↦ phi (x+(N*s)⁻¹ • z)
  have hF : ContDiffAt ℝ ∞ F v := (hp.contDiffAt (hU.mem_nhds hz)).comp v
    (contDiff_const.add (contDiff_id.const_smul _)).contDiffAt
  have hkle : (k:ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  have he : rescaledPhaseDefect phi L N s x =
      (fun z ↦ (N:ℂ) • (F z-phi x)) - (fun z ↦ (s⁻¹ • L) z) := rfl
  rw [he,iteratedFDeriv_sub_apply ((hF.sub contDiffAt_const).const_smul (N:ℂ) |>.of_le hkle)
    ((s⁻¹ • L).contDiff.contDiffAt.of_le hkle),iteratedFDeriv_linear_high _ _ hk,sub_zero,
    iteratedFDeriv_const_smul_apply' ((hF.sub contDiffAt_const).of_le hkle)]
  change ‖(N:ℂ) • iteratedFDeriv ℝ k (F - fun _ ↦ phi x) v‖ ≤ C/N
  rw [iteratedFDeriv_sub_apply (hF.of_le hkle) (contDiffAt_const.of_le hkle),
    iteratedFDeriv_const_of_ne (by omega : k ≠ 0)]
  simp only [Pi.zero_apply,sub_zero,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN0]
  have ha := affine_rescaling_derivative_power_on hU phi hp x v hr hz k
  calc
    _ ≤ N*(((N*s)⁻¹)^k*C) := mul_le_mul_of_nonneg_left
      (ha.trans (mul_le_mul_of_nonneg_left hb (by positivity))) hN0.le
    _ = (N*((N*s)⁻¹)^k)*C := by ring
    _ ≤ N⁻¹*C := mul_le_mul_of_nonneg_right (radius_high_power hN hs hk) hC
    _ = C/N := by ring

lemma rescaledAmplitudeRatio_high_bound {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (amp : _root_.OAI.Yau.Jets.Coord → ℂ) (ha : ContDiffOn ℝ ∞ amp U)
    {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) (x v : _root_.OAI.Yau.Jets.Coord)
    (hz : x+(N*s)⁻¹ • v ∈ U) (hax : (1/2:ℝ) ≤ ‖amp x‖)
    {k : ℕ} (hk : 1 ≤ k) {C : ℝ} (_ : 0 ≤ C)
    (hb : ‖iteratedFDeriv ℝ k amp (x+(N*s)⁻¹ • v)‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (rescaledAmplitudeRatio amp N s x) v‖ ≤ 2*C/N := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  obtain ⟨hr0,hr1,hNr⟩ := rescaling_radius_bound hN hs
  have hrN : (N*s)⁻¹ ≤ N⁻¹ :=
    (inv_le_inv₀ (mul_pos hN0 (lt_of_lt_of_le zero_lt_one hs)) hN0).mpr (by nlinarith)
  have hp : ((N*s)⁻¹)^k ≤ N⁻¹ :=
    (pow_le_pow_of_le_one hr0 hr1 hk).trans (by simpa using hrN)
  have hF : ContDiffAt ℝ ∞ (fun z ↦ amp (x+(N*s)⁻¹ • z)) v :=
    (ha.contDiffAt (hU.mem_nhds hz)).comp v (contDiff_const.add (contDiff_id.const_smul _)).contDiffAt
  have he : rescaledAmplitudeRatio amp N s x = fun z ↦ (amp x)⁻¹ • amp (x+(N*s)⁻¹ • z) := by
    funext z; simp [rescaledAmplitudeRatio,div_eq_mul_inv,mul_comm]
  rw [he,iteratedFDeriv_const_smul_apply' (hF.of_le (by
    exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))),norm_smul,norm_inv]
  have haxi : ‖amp x‖⁻¹ ≤ 2 := by
    have hh := (inv_le_inv₀ (by linarith : 0 < ‖amp x‖) (by norm_num : (0:ℝ) < 1/2)).mpr hax
    norm_num at hh
    exact hh
  have hf := affine_rescaling_derivative_power_on hU amp ha x v hr0 hz k
  calc
    _ ≤ 2*(N⁻¹*C) := mul_le_mul haxi (hf.trans (mul_le_mul hp hb (norm_nonneg _) (inv_nonneg.mpr hN0.le)))
      (norm_nonneg _) (by norm_num)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledJetDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

omit [CompactSpace T] in
lemma phase_smoothOn_target (t : T × Fin 3) :
    ContDiffOn ℝ ∞ (b.phase t) (b.F t).target :=
  (reval_contDiff _).comp_contDiffOn (b.chart_domain t).2.2

omit [CompactSpace T] in
lemma amplitude_smoothOn_target (N : ℝ) (t : T × Fin 3) :
    ContDiffOn ℝ ∞ (b.amplitude N t) (b.F t).target :=
  (finiteAmplitude_contDiff _ _ _).comp_contDiffOn (b.chart_domain t).2.2

theorem uniform_rescaled_factor_jets_oai (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) (d0 : ℕ) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ t x s, 1 ≤ s →
      sourceEuclideanNorm (x-y t.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R →
      let E := rescaledPhaseDefect (b.phase t)
        (frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))) n s x
      let A := rescaledAmplitudeRatio (b.amplitude n t) n s x
      ContDiffAt ℝ ∞ E v ∧ ContDiffAt ℝ ∞ A v ∧
      ∀ k, k ≤ d0 → ‖iteratedFDeriv ℝ k E v‖ ≤ e ∧
        ‖iteratedFDeriv ℝ k (fun z ↦ A z-1) v‖ ≤ e := by
  obtain ⟨delta,hd,C,hC,D,hD,hb⟩ := b.uniform_spatial_bounds hg hp hy d0
  obtain ⟨da,hda,Ca,hCa,Da,hDa,hab⟩ := b.uniform_amplitude_bounds hg hp hy
  filter_upwards [b.uniform_rescaled_phase_first hg hp hS hy hp0 R hR e he,
    b.uniform_main_amplitude_ratio hg hp hy R e he,eventually_shifted_main_distance R,
    eventually_nat_frequency (main_scale_eventually 2 1 (min delta da) (lt_min hd hda)),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2*C/e))]
    with n hfirst har hshift hn hlarge
  intro t x s hs hnear v hv
  have hN0 : 0 < (n:ℝ) := lt_of_lt_of_le zero_lt_one hn.1
  have hr : 0 < (n:ℝ)^(-5/12:ℝ) := Real.rpow_pos_of_pos hN0 _
  have hx := (norm_le_sourceEuclideanNorm _).trans hnear
  have hz := hshift s hs x (y t.1) v hv hnear
  have hzb := hb t _ (hz.trans (hn.2.1.trans (min_le_left _ _)))
  have hxa : ‖x-y t.1‖ ≤ da := by linarith [hn.2.1,min_le_right delta da]
  have hax := (hab t x hxa).2.2.2 n hn.1
  have hce : 2*C/(n:ℝ) ≤ e := (div_le_iff₀ hN0).mpr (by
    have := (div_le_iff₀ he).mp hlarge
    nlinarith)
  let E := rescaledPhaseDefect (b.phase t)
    (frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))) n s x
  let A := rescaledAmplitudeRatio (b.amplitude n t) n s x
  have hEs : ContDiffAt ℝ ∞ E v := rescaledPhaseDefect_smooth _ _ _ _ _ _ hzb.2.1
  have hAs : ContDiffAt ℝ ∞ A v := by
    dsimp [A,rescaledAmplitudeRatio]
    exact ((hzb.2.2.1 n).comp v (contDiff_const.add (contDiff_id.const_smul _)).contDiffAt).div_const _
  refine ⟨hEs,hAs,?_⟩
  intro k hk
  constructor
  · by_cases hk0 : k = 0
    · subst k
      simpa only [norm_iteratedFDeriv_zero] using (hfirst t x s hs hnear v hv).1
    by_cases hk1 : k = 1
    · subst k
      simpa only [norm_iteratedFDeriv_one] using (hfirst t x s hs hnear v hv).2
    have hh := rescaledPhaseDefect_high_bound (b.F t).open_target (b.phase t)
      (b.phase_smoothOn_target t)
      (frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))) hn.1 hs x v hzb.1 (by omega : 2 ≤ k) hC.le
      (hzb.2.2.2.1 k hk)
    exact hh.trans ((div_le_div_of_nonneg_right (by linarith : C ≤ 2*C) hN0.le).trans hce)
  · by_cases hk0 : k = 0
    · subst k
      simpa only [norm_iteratedFDeriv_zero,rescaledAmplitudeRatio] using (har t x s hs hnear v hv).2.1
    have hkf : (k:ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
    change ‖iteratedFDeriv ℝ k (A - fun _ ↦ 1) v‖ ≤ e
    rw [iteratedFDeriv_sub_apply (hAs.of_le hkf) (contDiffAt_const.of_le hkf),
      iteratedFDeriv_const_of_ne hk0]
    simp only [Pi.zero_apply,sub_zero]
    exact (rescaledAmplitudeRatio_high_bound (b.F t).open_target (b.amplitude n t)
      (b.amplitude_smoothOn_target n t) hn.1 hs x v hzb.1 hax.2.2.1
      (by omega : 1 ≤ k) hC.le (hzb.2.2.2.2.1 n hn.1 k hk)).trans hce

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Yau.Geometry.TripleSourceWaveData.uniform_rescaled_factor_jets_oai.{u_1} := @OAI.Yau.Geometry.TripleSourceWaveData.uniform_rescaled_factor_jets_oai.{u_1}
