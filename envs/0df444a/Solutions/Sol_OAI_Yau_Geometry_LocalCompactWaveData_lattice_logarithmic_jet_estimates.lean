-- Prove2me | solution 1 for OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:27:45.603455+00:00
-- url     : https://prove2.me/submissions/299c46ec-2f54-4898-adcf-d06b1fc685f1

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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_TripleSourceWaveData_real_defect_second

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_JetCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

lemma homogeneousComponent_pderiv (p : CPoly) (n : ℕ) (i : Fin 4) :
    homogeneousComponent n (pderiv i p) = pderiv i (homogeneousComponent (n + 1) p) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_pderiv, map_add, Finsupp.degree_single]
  by_cases hd : d.degree = n
  · simp [hd]
  · simp [hd]

end
end Yau.Jets

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

theorem fderiv_reval (p : CPoly) (x v : Coord) :
    fderiv ℝ (reval p) x v = ∑ i, reval (pderiv i p) x * (v i : ℂ) := by
  have hd (p : CPoly) : DifferentiableAt ℝ (reval p) x :=
    (reval_contDiff p).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have he : reval (C a) = fun _ ↦ a := by ext; simp [reval]
    rw [he]
    simp [reval]
  | add p q hp hq =>
    have he : reval (p + q) = fun x ↦ reval p x + reval q x := by ext; simp [reval]
    rw [he]
    change (fderiv ℝ (reval p + reval q) x) v = _
    rw [fderiv_add (hd p) (hd q)]
    simp only [add_apply, hp, hq, map_add, reval, add_mul,
      Finset.sum_add_distrib]
  | mul_X p j hp =>
    have he : reval (p * X j) = fun x ↦ reval p x * coordCLM j x := by
      ext; simp [reval, coordCLM]
    rw [he]
    change (fderiv ℝ (reval p * ⇑(coordCLM j)) x) v = _
    rw [fderiv_mul (hd p) (coordCLM j).differentiableAt]
    simp [hp, reval, coordCLM, pderiv_X, Finset.sum_add_distrib,
      Finset.mul_sum, mul_add, mul_comm, mul_left_comm, Pi.single_apply, apply_ite]

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

lemma frameMap_axis (e : Fin 4 → _root_.OAI.Yau.Jets.Coord) (i : Fin 4) : frameMap e (Pi.single i 1) = e i := by
  simp [frameMap_apply, Pi.single_apply, ite_smul, eq_comm]

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_InitialPhasePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

lemma pderiv_linearPhase (v : Fin 4 → ℂ) (i : Fin 4) :
    pderiv i (linearPhase v) = C (v i) := by
  simp [linearPhase, pderiv_X, Pi.single_apply]

lemma initialPhaseJet_first (S : ℝ) (v : Fin 4 → ℂ) (H : Fin 4 → Fin 4 → ℂ) (i : Fin 4) :
    pderiv i (initialPhaseJet S v H 1) = C (v i) := by
  simpa [initialPhaseJet] using pderiv_linearPhase v i

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PhaseActualJet
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

lemma reval_zero_homogeneous (p : CPoly) :
    reval p 0 = reval (homogeneousComponent 0 p) 0 := by
  simp [reval, constantCoeff_eq]

lemma retained_phase_value (p : CPoly) (s : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ)
    (h : homogeneousComponent 0 p = initialPhaseJet s v H 0) : reval p 0 = (s:ℂ) := by
  rw [reval_zero_homogeneous, h]
  simp [initialPhaseJet, reval]

lemma retained_phase_first (p : CPoly) (s : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ)
    (h : homogeneousComponent 1 p = initialPhaseJet s v H 1) (i : Fin 4) :
    reval (pderiv i p) 0 = v i := by
  rw [reval_zero_homogeneous, homogeneousComponent_pderiv, show 0+1=1 from rfl, h,
    initialPhaseJet_first]
  simp [reval]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartedEnvelope
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma metricGradient_pair (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v) (v : _root_.OAI.Yau.Jets.Coord) :
    g y (metricGradient g S y) v = fderiv ℝ S y v := by
  have hi : ContinuousLinearMap.inverse (g y) = (positiveMetricEquiv (g y) hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv (g y) hp)
  change positiveMetricEquiv (g y) hp (ContinuousLinearMap.inverse (g y) (fderiv ℝ S y)) v = _
  rw [hi, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientLocality
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma metricGradient_eventuallyEq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S A : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    metricGradient g S =ᶠ[𝓝 x] metricGradient G A := by
  filter_upwards [hg,hS.fderiv (𝕜 := ℝ)] with z hz hd
  simp only [metricGradient,hz,hd]

lemma sourceHessian_eventuallyEq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S A : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hS : S =ᶠ[𝓝 x] A) :
    sourceHessian g S =ᶠ[𝓝 x] sourceHessian G A := by
  filter_upwards [hg,hg.fderiv (𝕜 := ℝ),hS.fderiv (𝕜 := ℝ),
    (hS.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)] with z hz hd hs hss
  simp only [sourceHessian,hz,hd,hs,hss]

end
end Yau.Geometry

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AdmissibleDirectionTriple
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
attribute [local instance] clmTopology clmAdd clmModule

lemma frame_pair_coordinate (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (ho : ∀ i j : Fin 4, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (i : Fin 4) (v : _root_.OAI.Yau.Jets.Coord) : g (e (Pi.single i 1)) v = e.symm v i := by
  calc
    _ = g (e (Pi.single i 1)) (e (e.symm v)) := by rw [e.apply_symm_apply]
    _ = _ := by
      have hexp : e.symm v = ∑ j : Fin 4, e.symm v j • Pi.single j (1:ℝ) := by
        ext j; simp [Pi.single_apply]
      conv_lhs => rw [hexp]
      simp [map_sum,map_smul,ho,smul_eq_mul]

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

lemma frame_orthonormal (z : T × Fin 3) (i j : Fin 4) :
    g z.1 (d.frame z (Pi.single i 1)) (d.frame z (Pi.single j 1)) = if i=j then 1 else 0 := by
  change g z.1 (frameMap (d.e z.1 z.2) (Pi.single i 1))
    (frameMap (d.e z.1 z.2) (Pi.single j 1)) = _
  simp only [frameMap_axis,d.orthonormal]

lemma frame_first (hpos : ∀ t v, v ≠ 0 → 0 < g t v v) (hp0 : ∀ t, p t ≠ 0)
    (z : T × Fin 3) : alpha (g := g) (p := p) z.1 • d.frame z (Pi.single 0 1) = p z.1 := by
  change alpha z.1 • frameMap (d.e z.1 z.2) (Pi.single 0 1) = _
  rw [frameMap_axis,d.first]
  simp [alpha,metricNormalize,smul_smul,ne_of_gt (Real.sqrt_pos.mpr (hpos z.1 _ (hp0 z.1)))]

lemma frame_second (hpos : ∀ t v, v ≠ 0 → 0 < g t v v) (hp0 : ∀ t, p t ≠ 0)
    (z : T × Fin 3) : beta (g := g) (p := p) z.1 • d.frame z (Pi.single 1 1) = d.q z.1 z.2 := by
  have hb : 0 < g z.1 (p z.1) (p z.1)+4 := by have h := hpos z.1 _ (hp0 z.1); linarith
  change beta z.1 • frameMap (d.e z.1 z.2) (Pi.single 1 1) = _
  rw [frameMap_axis,d.second]
  simp [beta,metricNormalize,d.length,smul_smul,ne_of_gt (Real.sqrt_pos.mpr hb)]
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

lemma center_mem_target (t : T × Fin 3) : y t.1 ∈ (b.F t).target := by
  rw [← b.chart_zero t]
  exact (b.F t).map_source (b.zero_mem_source t)

lemma inverse_center (t : T × Fin 3) : (b.F t).symm (y t.1) = 0 := by
  rw [← b.chart_zero t]
  exact (b.F t).left_inv (b.zero_mem_source t)

lemma inverse_derivative (t : T × Fin 3) :
    HasFDerivAt ((b.F t).symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (d.frame t).symm.toContinuousLinearMap (y t.1) := by
  apply (b.F t).hasFDerivAt_symm (b.center_mem_target t)
  rw [b.inverse_center,b.chart_eq]
  exact quadraticChartMap_deriv_zero _ _ _

lemma phase_smooth_at_center (t : T × Fin 3) : ContDiffAt ℝ ∞ (b.phase t) (y t.1) :=
  (reval_contDiff _).contDiffAt.comp _ ((b.chart_domain t).2.2.contDiffAt
    ((b.F t).open_target.mem_nhds (b.center_mem_target t)))

lemma phase_center (t : T × Fin 3) : b.phase t (y t.1) = (S (y t.1):ℂ) := by
  unfold phase
  simp only [Function.comp_apply,b.inverse_center]
  exact retained_phase_value _ _ _ _ (b.jets.phase_retained t 0 (by omega))

lemma amplitude_center (N : ℝ) (t : T × Fin 3) : b.amplitude N t (y t.1) = 1 := by
  unfold amplitude
  simp only [Function.comp_apply,b.inverse_center]
  exact finiteAmplitude_center _ _ _ (fun j ↦ b.jets.amplitude_value j t)

lemma phase_first (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (b.phase t) (y t.1) v =
      (g (y t.1) (metricGradient g S (y t.1)) v:ℂ) +
        Complex.I * (g (y t.1) (d.q t.1 t.2) v:ℂ) := by
  have hder := ((reval_contDiff (b.phi t)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasFDerivAt
  have he := (b.inverse_derivative t)
  have hf : fderiv ℝ (b.phase t) (y t.1) v =
      fderiv ℝ (reval (b.phi t)) 0 ((d.frame t).symm v) := by
    unfold phase
    rw [fderiv_comp _ (by rw [b.inverse_center]; exact hder.differentiableAt) he.differentiableAt,
      he.fderiv,b.inverse_center]
    rfl
  rw [hf,fderiv_reval]
  simp_rw [retained_phase_first _ _ _ _ (b.jets.phase_retained t 1 (by omega))]
  have hpair0 : g (y t.1) (metricGradient g S (y t.1)) v =
      sourceTripleAlpha g S y t * (d.frame t).symm v 0 := by
    have hframe : sourceTripleAlpha g S y t • d.frame t (Pi.single 0 1) = metricGradient g S (y t.1) :=
      d.frame_first (fun t ↦ hpos (y t)) hp0 t
    rw [← hframe]
    simp only [map_smul,smul_apply,smul_eq_mul]
    rw [frame_pair_coordinate (g (y t.1)) (d.frame t) (d.frame_orthonormal t)]
  have hpair1 : g (y t.1) (d.q t.1 t.2) v =
      sourceTripleBeta g S y t * (d.frame t).symm v 1 := by
    have hframe : sourceTripleBeta g S y t • d.frame t (Pi.single 1 1) = d.q t.1 t.2 :=
      d.frame_second (fun t ↦ hpos (y t)) hp0 t
    rw [← hframe]
    simp only [map_smul,smul_apply,smul_eq_mul]
    rw [frame_pair_coordinate (g (y t.1)) (d.frame t) (d.frame_orthonormal t)]
  rw [hpair0,hpair1]
  simp [normalFrameVector,Fin.sum_univ_succ]
  ring

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_QuadraticTaylorBound
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

lemma first_order_remainder_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : _root_.OAI.Yau.Jets.Coord → E) (y : _root_.OAI.Yau.Jets.Coord) (r C : ℝ) (hC : 0 ≤ C)
    (hs : ∀ z, ‖z-y‖ ≤ r → ContDiffAt ℝ ∞ f z)
    (hb : ∀ z, ‖z-y‖ ≤ r → ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C)
    (x : _root_.OAI.Yau.Jets.Coord) (hx : ‖x-y‖ ≤ r) :
    ‖f x-f y-fderiv ℝ f y (x-y)‖ ≤ C*‖x-y‖^2 := by
  let R := ‖x-y‖
  have hR : 0 ≤ R := norm_nonneg _
  have h0 : ‖y-y‖ ≤ r := by simpa using hR.trans hx
  have hd (z : _root_.OAI.Yau.Jets.Coord) (hz : ‖z-y‖ ≤ R) :
      ‖fderiv ℝ f z - fderiv ℝ f y‖ ≤ C*‖z-y‖ :=
    norm_sub_le_on_closedBall (fderiv ℝ f) y R C hC
      (fun v hv ↦ ((hs v (hv.trans hx)).fderiv_right (by simp) :
        ContDiffAt ℝ ∞ (fderiv ℝ f) v).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (fun v hv ↦ hb v (hv.trans hx)) hR z hz
  let q : _root_.OAI.Yau.Jets.Coord → E := fun z ↦ f z-f y-fderiv ℝ f y (z-y)
  have hq (z : _root_.OAI.Yau.Jets.Coord) (hz : ‖z-y‖ ≤ R) :
      HasFDerivAt q (fderiv ℝ f z-fderiv ℝ f y) z := by
    have h := ((hs z (hz.trans hx)).differentiableAt (by simp)).hasFDerivAt
    convert (h.sub_const (f y)).sub ((fderiv ℝ f y).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const y)) using 1 <;> rfl
  have hrem := norm_sub_le_on_closedBall q y R (C*R) (mul_nonneg hC hR)
    (fun z hz ↦ (hq z hz).differentiableAt)
    (fun z hz ↦ by rw [(hq z hz).fderiv]; exact (hd z hz).trans (mul_le_mul_of_nonneg_left hz hC))
    hR x le_rfl
  simpa [q,R,pow_two,mul_assoc] using hrem

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealPhaseJet
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

lemma realPart_fderiv (f : _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord) (hf : DifferentiableAt ℝ f x) (v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fun z ↦ (f z).re) x v = (fderiv ℝ f x v).re := by
  change fderiv ℝ (Complex.reCLM ∘ f) x v = _
  rw [(Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

lemma realPart_iterated_norm_le (f : _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hf : ContDiffAt ℝ ∞ f x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ (f z).re) x‖ ≤ ‖iteratedFDeriv ℝ k f x‖ := by
  have he := Complex.reCLM.iteratedFDeriv_comp_left hf
    (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))
  change iteratedFDeriv ℝ k (fun z ↦ (f z).re) x = _ at he
  rw [he]
  have hr : ‖Complex.reCLM‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z ↦ by simpa using Complex.abs_re_le_norm z)
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right hr (norm_nonneg (iteratedFDeriv ℝ k f x)))

variable {T : Type*} [TopologicalSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

lemma real_phase_first (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fun z ↦ (b.phase t z).re) (y t.1) v = fderiv ℝ S (y t.1) v := by
  rw [realPart_fderiv _ _ ((b.phase_smooth_at_center t).differentiableAt (by simp)),
    b.phase_first hp hp0,metricGradient_pair g S _ (hp _) v]
  simp

lemma real_defect_first (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hS : ContDiff ℝ ∞ S) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) :
    fderiv ℝ (b.realDefect t) (y t.1) = 0 := by
  have hs : ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) (y t.1) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ (b.phase_smooth_at_center t)
  unfold realDefect
  rw [fderiv_fun_sub (hs.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hS.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)]
  ext v
  simp only [sub_apply,zero_apply]
  rw [b.real_phase_first hp hp0]
  ring

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PhaseBounds
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

lemma compact_moving_derivative_bound {T E : Type*} [TopologicalSpace T] [CompactSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : _root_.OAI.Yau.Jets.Coord → E) (hf : ContDiff ℝ ∞ f) (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (r : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ t x, ‖x-y t‖ ≤ r → ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  have hc : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ k f (y z.1+z.2)) :=
    (hf.continuous_iteratedFDeriv (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).comp
      ((hy.comp continuous_fst).add continuous_snd)
  obtain ⟨C,hC,hb⟩ := ((isCompact_univ.prod (isCompact_closedBall (0:_root_.OAI.Yau.Jets.Coord) r)).image hc).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro t x hx
  have hh := hb _ (show iteratedFDeriv ℝ k f (y t+(x-y t)) ∈
      (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ k f (y z.1+z.2)) '' (univ ×ˢ closedBall 0 r) from
    ⟨(t,x-y t),⟨mem_univ _,by simpa using hx⟩,rfl⟩)
  simpa using hh

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_phase_gradient_remainders (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hS : ContDiff ℝ ∞ S) (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) :
    ∃ delta > 0, ∃ C > 0, ∀ t x v, ‖x-y t.1‖ ≤ delta →
      |(fderiv ℝ (b.phase t) x v).re - (fderiv ℝ S x v-b.eta t*g (y t.1) (x-y t.1) v)| ≤
        C*‖x-y t.1‖^2*‖v‖ ∧
      |(fderiv ℝ (b.phase t) x v).im - g (y t.1) (d.q t.1 t.2) v| ≤ C*‖x-y t.1‖*‖v‖ := by
  obtain ⟨delta,hd,Cp,hCp,D,hD,hb⟩ := b.uniform_spatial_bounds hg hp hy 3
  obtain ⟨Cs,hCs,hSb⟩ := compact_moving_derivative_bound S hS y hy delta 3
  have hf (t : T × Fin 3) (x : _root_.OAI.Yau.Jets.Coord) (hx : ‖x-y t.1‖ ≤ delta) :
      ContDiffAt ℝ ∞ (b.realDefect t) x :=
    (Complex.reCLM.contDiff.contDiffAt.comp _ (hb t x hx).2.1).sub hS.contDiffAt
  have hthird (t : T × Fin 3) (x : _root_.OAI.Yau.Jets.Coord) (hx : ‖x-y t.1‖ ≤ delta) :
      ‖iteratedFDeriv ℝ 3 (b.realDefect t) x‖ ≤ Cp+Cs := by
    have hphi := (hb t x hx).2.1
    have hrp : ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) x :=
      Complex.reCLM.contDiff.contDiffAt.comp _ hphi
    change ‖iteratedFDeriv ℝ 3 ((fun z ↦ (b.phase t z).re)-S) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply
      (hrp.of_le
        (by change (↑(3:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
      (hS.contDiffAt.of_le (by change (↑(3:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))]
    exact (norm_sub_le _ _).trans (add_le_add
      ((realPart_iterated_norm_le _ _ hphi 3).trans ((hb t x hx).2.2.2.1 3 le_rfl)) (hSb t.1 x hx))
  refine ⟨delta,hd,Cp+Cs,by positivity,?_⟩
  intro t x v hx
  have hq := first_order_remainder_bound (fderiv ℝ (b.realDefect t)) (y t.1) delta (Cp+Cs)
    (by positivity) (fun z hz ↦ (hf t z hz).fderiv_right (by simp))
    (fun z hz ↦ by
      rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv]
      exact hthird t z hz) x hx
  have hv := (fderiv ℝ (b.realDefect t) x - fderiv ℝ (b.realDefect t) (y t.1) -
    fderiv ℝ (fderiv ℝ (b.realDefect t)) (y t.1) (x-y t.1)).le_opNorm v
  have hvb := hv.trans (mul_le_mul_of_nonneg_right hq (norm_nonneg v))
  rw [b.real_defect_first hp hS hp0] at hvb
  simp only [sub_zero,sub_apply] at hvb
  rw [b.real_defect_second hg hs hp hS hp0] at hvb
  have hdx : fderiv ℝ (b.realDefect t) x v = (fderiv ℝ (b.phase t) x v).re-fderiv ℝ S x v := by
    have hrp : ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) x :=
      Complex.reCLM.contDiff.contDiffAt.comp _ (hb t x hx).2.1
    unfold realDefect
    rw [fderiv_fun_sub
      (hrp.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hS.differentiable (by simp) x),sub_apply,
      realPart_fderiv _ _ ((hb t x hx).2.1.differentiableAt (by simp))]
  rw [hdx] at hvb
  have hreal : |(fderiv ℝ (b.phase t) x v).re - (fderiv ℝ S x v-b.eta t*g (y t.1) (x-y t.1) v)| ≤
      (Cp+Cs)*‖x-y t.1‖^2*‖v‖ := by
    convert hvb using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hphi := norm_sub_le_on_closedBall (fderiv ℝ (b.phase t)) (y t.1) delta Cp hCp.le
    (fun z hz ↦ (((hb t z hz).2.1.fderiv_right (by simp)) :
      ContDiffAt ℝ ∞ (fderiv ℝ (b.phase t)) z).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun z hz ↦ by
      rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
      exact (hb t z hz).2.2.2.1 2 (by omega)) hd.le x hx
  have hvec := ((fderiv ℝ (b.phase t) x-fderiv ℝ (b.phase t) (y t.1)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hphi (norm_nonneg v))
  have him := (Complex.abs_im_le_norm _).trans hvec
  simp only [sub_apply,Complex.sub_im] at him
  rw [b.phase_first hp hp0] at him
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,zero_mul,one_mul,zero_add] at him
  exact ⟨hreal,him.trans (by gcongr; linarith)⟩

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FrozenPhaseLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets Set Metric
open scoped ContDiff

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_real_phase_value_bound (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) :
    ∃ delta > 0, ∃ C > 0, ∀ t x, ‖x-y t.1‖ ≤ delta →
      |(b.phase t x).re-S x| ≤ C*‖x-y t.1‖^2 := by
  obtain ⟨delta,hd,Cp,hCp,D,hD,hb⟩ := b.uniform_spatial_bounds hg hp hy 2
  obtain ⟨Cs,hCs,hSb⟩ := compact_moving_derivative_bound S hS y hy delta 2
  have hrp (t : T × Fin 3) (x : _root_.OAI.Yau.Jets.Coord) (hx : ‖x-y t.1‖ ≤ delta) :
      ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp _ (hb t x hx).2.1
  have hsecond (t : T × Fin 3) (x : _root_.OAI.Yau.Jets.Coord) (hx : ‖x-y t.1‖ ≤ delta) :
      ‖iteratedFDeriv ℝ 2 (b.realDefect t) x‖ ≤ Cp+Cs := by
    change ‖iteratedFDeriv ℝ 2 ((fun z ↦ (b.phase t z).re)-S) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply
      ((hrp t x hx).of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
      (hS.contDiffAt.of_le (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))]
    exact (norm_sub_le _ _).trans (add_le_add
      ((realPart_iterated_norm_le _ _ (hb t x hx).2.1 2).trans ((hb t x hx).2.2.2.1 2 le_rfl)) (hSb t.1 x hx))
  refine ⟨delta,hd,Cp+Cs,by positivity,?_⟩
  intro t x hx
  have hq := first_order_remainder_bound (b.realDefect t) (y t.1) delta (Cp+Cs)
    (by positivity) (fun z hz ↦ (hrp t z hz).sub hS.contDiffAt)
    (fun z hz ↦ by
      rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
      exact hsecond t z hz) x hx
  rw [b.real_defect_first hp hS hp0] at hq
  have hc : b.realDefect t (y t.1) = 0 := by simp [realDefect,b.phase_center]
  rw [hc] at hq
  simpa [realDefect] using hq

end TripleSourceWaveData

end Yau.Geometry

end

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

lemma half_scale_square {N : ℝ} (hN : 0 < N) : (N^(-1/2:ℝ))^2 = N⁻¹ := by
  rw [← Real.rpow_mul_natCast hN.le]
  norm_num
  exact Real.rpow_neg_one N

lemma inverse_le_half_scale {N : ℝ} (hN : 1 ≤ N) : N⁻¹ ≤ N^(-1/2:ℝ) := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

lemma half_scale_eventually (L D delta : ℝ) (hd : 0 < delta) :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧ L*N^(-1/2:ℝ) ≤ delta ∧
      D*(L*N^(-1/2:ℝ)) < N^(-1/3:ℝ) := by
  have hsmall : Tendsto (fun N : ℝ ↦ L*N^(-1/2:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).const_mul L
  have hcut : Tendsto (fun N : ℝ ↦ (D*L)*N^(-1/6:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/6)).const_mul (D*L)
  filter_upwards [eventually_ge_atTop (1:ℝ),hsmall.eventually (gt_mem_nhds hd),
    hcut.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with N hN hs hc
  refine ⟨hN,hs.le,?_⟩
  have hp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have he : N^(-1/2:ℝ) = N^(-1/6:ℝ)*N^(-1/3:ℝ) := by
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

lemma amplitude_exp_log_jet (a phi V : _root_.OAI.Yau.Jets.Coord → ℂ) (N : ℝ) (hN : N ≠ 0)
    (x : _root_.OAI.Yau.Jets.Coord) (ha : DifferentiableAt ℝ a x) (hp : DifferentiableAt ℝ phi x)
    (hn : a x ≠ 0)
    (he : V =ᶠ[𝓝 x] (fun z ↦ a z * Complex.exp ((N:ℂ)*phi z))) (v : _root_.OAI.Yau.Jets.Coord) :
    normalizedLogJet N V x v = fderiv ℝ phi x v + (N:ℂ)⁻¹*(fderiv ℝ a x v/a x) := by
  have hd := ha.hasFDerivAt.mul ((hp.hasFDerivAt.const_mul (N:ℂ)).cexp)
  change HasFDerivAt (fun z ↦ a z * Complex.exp ((N:ℂ)*phi z)) _ x at hd
  have hnc : (N:ℂ) ≠ 0 := by exact_mod_cast hN
  unfold normalizedLogJet
  rw [he.fderiv_eq,he.self_of_nhds,hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  field_simp [hn,Complex.exp_ne_zero,hnc]

lemma log_amplitude_correction_bound (a da : ℂ) (N C : ℝ) (hN : 0 < N)
    (hC : 0 ≤ C) (ha : (1/2:ℝ) ≤ ‖a‖) (hd : ‖da‖ ≤ C) :
    ‖(N:ℂ)⁻¹*(da/a)‖ ≤ 2*C/N := by
  rw [norm_mul,norm_inv,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  have hb : ‖da‖ / ‖a‖ ≤ 2*C := (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  calc
    N⁻¹*(‖da‖/‖a‖) ≤ N⁻¹*(2*C) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hN.le)
    _ = _ := by ring

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

lemma wave_log_jet (N : ℝ) (hN : 0 < N) (t : T × Fin 3) (x v : _root_.OAI.Yau.Jets.Coord)
    (hx : x ∈ (b.F t).target) (hsmall : ‖(b.F t).symm x‖ < N^(-1/3:ℝ))
    (ha : b.amplitude N t x ≠ 0) :
    b.wave N t x ≠ 0 ∧ normalizedLogJet N (b.wave N t) x v =
      fderiv ℝ (b.phase t) x v + (N:ℂ)⁻¹*(fderiv ℝ (b.amplitude N t) x v/b.amplitude N t x) := by
  have hInv := (b.chart_domain t).2.2.contDiffAt ((b.F t).open_target.mem_nhds hx)
  have hag := (finiteAmplitude_contDiff (fun j ↦ b.A j t) J N).contDiffAt.comp x hInv
  have hpg := (reval_contDiff (b.phi t)).contDiffAt.comp x hInv
  have he := b.wave_germ_of_small_inverse N hN t x hx hsmall
  refine ⟨?_,amplitude_exp_log_jet _ _ _ N hN.ne' x
    (hag.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hpg.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ha he v⟩
  rw [he.self_of_nhds]
  exact mul_ne_zero ha (Complex.exp_ne_zero _)

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LogJetBounds
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
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_logarithmic_jet_estimates (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hS : ContDiff ℝ ∞ S) (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (L : ℝ) (hL : 0 < L) :
    ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0, ∀ᶠ N : ℝ in atTop, ∀ t x,
      ‖x-y t.1‖ ≤ L*N^(-1/2:ℝ) →
      ‖b.amplitude N t x-1‖ ≤ Ca*N^(-1/2:ℝ) ∧
      (1/2:ℝ) ≤ ‖b.amplitude N t x‖ ∧ ‖b.amplitude N t x‖ ≤ 3/2 ∧
      b.wave N t x ≠ 0 ∧ ∀ v,
      |(normalizedLogJet N (b.wave N t) x v).re -
        (fderiv ℝ S x v-b.eta t*g (y t.1) (x-y t.1) v)| ≤ Cr/N*‖v‖ ∧
      |(normalizedLogJet N (b.wave N t) x v).im - g (y t.1) (d.q t.1 t.2) v| ≤
        Ci*N^(-1/2:ℝ)*‖v‖ := by
  obtain ⟨ra,hra,A,hA,D,hD,ha⟩ := b.uniform_amplitude_bounds hg hp hy
  obtain ⟨rp,hrp,P,hP,hphase⟩ := b.uniform_phase_gradient_remainders hg hs hp hS hy hp0
  refine ⟨A*L,by positivity,P*L^2+2*A,by positivity,P*L+2*A,by positivity,?_⟩
  filter_upwards [half_scale_eventually L D (min ra rp) (lt_min hra hrp)] with N hn
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hn.1
  intro t x hx
  have hxa : ‖x-y t.1‖ ≤ ra := (hx.trans hn.2.1).trans (min_le_left _ _)
  have hxp : ‖x-y t.1‖ ≤ rp := (hx.trans hn.2.1).trans (min_le_right _ _)
  obtain ⟨hxt,hInv,_,hamp⟩ := ha t x hxa
  obtain ⟨hsm,hnear,hlo,hup,hne,hder⟩ := hamp N hn.1
  have hcut : ‖(b.F t).symm x‖ < N^(-1/3:ℝ) :=
    (hInv.trans (mul_le_mul_of_nonneg_left hx (by linarith))).trans_lt hn.2.2
  have hsq : ‖x-y t.1‖^2 ≤ L^2/N := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hx 2
    rw [mul_pow,half_scale_square hN] at hh
    simpa only [div_eq_mul_inv] using hh
  have hnear' : ‖b.amplitude N t x-1‖ ≤ (A*L)*N^(-1/2:ℝ) :=
    hnear.trans (by calc
      A*‖x-y t.1‖ ≤ A*(L*N^(-1/2:ℝ)) := mul_le_mul_of_nonneg_left hx hA.le
      _ = _ := by ring)
  refine ⟨hnear',hlo,hup,(b.wave_log_jet N hN t x 0 hxt hcut hne).1,?_⟩
  intro v
  have he := (b.wave_log_jet N hN t x v hxt hcut hne).2
  have hc := log_amplitude_correction_bound (b.amplitude N t x)
    (fderiv ℝ (b.amplitude N t) x v) N (A*‖v‖) hN (by positivity) hlo
    (((fderiv ℝ (b.amplitude N t) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hder (norm_nonneg v)))
  obtain ⟨hr,hi⟩ := hphase t x v hxp
  rw [he,Complex.add_re,Complex.add_im]
  constructor
  · have hcR := (Complex.abs_re_le_norm _).trans hc
    calc
      _ = |((fderiv ℝ (b.phase t) x v).re-(fderiv ℝ S x v-b.eta t*g (y t.1) (x-y t.1) v))+
          ((N:ℂ)⁻¹*(fderiv ℝ (b.amplitude N t) x v/b.amplitude N t x)).re| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hr hcR)
      _ ≤ P*(L^2/N)*‖v‖+2*(A*‖v‖)/N := by gcongr
      _ = _ := by ring
  · have hcI := (Complex.abs_im_le_norm _).trans hc
    calc
      _ = |((fderiv ℝ (b.phase t) x v).im-g (y t.1) (d.q t.1 t.2) v)+
          ((N:ℂ)⁻¹*(fderiv ℝ (b.amplitude N t) x v/b.amplitude N t x)).im| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hi hcI)
      _ = P*‖x-y t.1‖*‖v‖+(2*A*‖v‖)*N⁻¹ := by ring
      _ ≤ P*(L*N^(-1/2:ℝ))*‖v‖+(2*A*‖v‖)*N^(-1/2:ℝ) := by
        gcongr
        exact inverse_le_half_scale hn.1
      _ = _ := by ring

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ScalarBounds
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

lemma exp_wave_relative_norm (a phi : ℂ) (N S : ℝ) :
    ‖a*Complex.exp ((N:ℂ)*phi)‖*Real.exp (-N*S) = ‖a‖*Real.exp (N*(phi.re-S)) := by
  rw [norm_mul,Complex.norm_exp,mul_assoc,← Real.exp_add]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  congr 2
  ring

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_relative_wave_bounds (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (L : ℝ) (hL : 0 < L) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t x, ‖x-y t.1‖ ≤ L*N^(-1/2:ℝ) →
      c ≤ ‖b.wave N t x‖*Real.exp (-N*S x) ∧ ‖b.wave N t x‖*Real.exp (-N*S x) ≤ C := by
  obtain ⟨ra,hra,A,hA,D,hD,ha⟩ := b.uniform_amplitude_bounds hg hp hy
  obtain ⟨rp,hrp,P,hP,hphase⟩ := b.uniform_real_phase_value_bound hg hp hS hy hp0
  refine ⟨(1/2)*Real.exp (-P*L^2),by positivity,(3/2)*Real.exp (P*L^2),by positivity,?_⟩
  filter_upwards [half_scale_eventually L D (min ra rp) (lt_min hra hrp)] with N hn
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hn.1
  intro t x hx
  have hxa := (hx.trans hn.2.1).trans (min_le_left ra rp)
  have hxp := (hx.trans hn.2.1).trans (min_le_right ra rp)
  obtain ⟨hxt,hInv,_,hamp⟩ := ha t x hxa
  obtain ⟨_,_,hlo,hup,_,_⟩ := hamp N hn.1
  have hcut : ‖(b.F t).symm x‖ < N^(-1/3:ℝ) :=
    (hInv.trans (mul_le_mul_of_nonneg_left hx (by linarith))).trans_lt hn.2.2
  rw [(b.wave_germ_of_small_inverse N hN t x hxt hcut).self_of_nhds,exp_wave_relative_norm]
  have hsq : ‖x-y t.1‖^2 ≤ L^2/N := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hx 2
    rw [mul_pow,half_scale_square hN] at hh
    simpa only [div_eq_mul_inv] using hh
  have hb := (hphase t x hxp).trans (mul_le_mul_of_nonneg_left hsq hP.le)
  have hb' := mul_le_mul_of_nonneg_left hb hN.le
  have hnabs : |N*((b.phase t x).re-S x)| ≤ P*L^2 := by
    rw [abs_mul,abs_of_pos hN]
    calc
      _ ≤ N*(P*(L^2/N)) := hb'
      _ = _ := by field_simp
  obtain ⟨hl,hu⟩ := abs_le.mp hnabs
  constructor
  · exact mul_le_mul hlo (Real.exp_le_exp.mpr (by linarith)) (by positivity) (norm_nonneg _)
  · exact mul_le_mul hup (Real.exp_le_exp.mpr hu) (by positivity) (by norm_num)

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeSourceWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

lemma selectFrame_center (d : SourceCompactFrameCover g S D) (x : D) :
    coverSourceCenter d (selectFrame d x) = x :=
  congrArg Subtype.val (Classical.choose_spec (d.surjective_center x))

lemma latticeFrame_center (d : SourceCompactFrameCover g S D) (hUD : U ⊆ D)
    (n : ℕ) (z : SourceGrid U n) :
    coverSourceCenter d (latticeFrame d hUD n z) = scaledLatticePoint n z :=
  selectFrame_center d _

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LocalWaveJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma center_identifications (t : a.cover.Parameter) :
    a.G (coverSourceCenter a.cover t) = g (coverSourceCenter a.cover t) ∧
    a.A (coverSourceCenter a.cover t) = S (coverSourceCenter a.cover t) ∧
    metricGradient a.G a.A (coverSourceCenter a.cover t) = metricGradient g S (coverSourceCenter a.cover t) ∧
    sourceHessian a.G a.A (coverSourceCenter a.cover t) = sourceHessian g S (coverSourceCenter a.cover t) := by
  obtain ⟨hG,hW,hA⟩ := a.germ _ (a.centers_E (a.cover.center t).property)
  exact ⟨hG.self_of_nhds,hA.self_of_nhds,(metricGradient_eventuallyEq hG hA).self_of_nhds,
    (sourceHessian_eventuallyEq hG hA).self_of_nhds⟩

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalLogJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma eta_original (t : a.cover.Parameter × Fin 3) : a.beams.eta t = a.originalEta t := by
  unfold TripleSourceWaveData.eta originalEta
  rw [(a.center_identifications t.1).1,(a.center_identifications t.1).2.2.1,
    (a.center_identifications t.1).2.2.2]

lemma common_original_neighborhood : ∃ r > 0, ∀ t : a.cover.Parameter, ∀ x,
    ‖x-coverSourceCenter a.cover t‖ ≤ r → x ∈ a.E := by
  obtain ⟨r,hr,hri⟩ := compact_family_common_radius isCompact_univ
    (fun z : a.cover.Parameter × _root_.OAI.Yau.Jets.Coord ↦ coverSourceCenter a.cover z.1+z.2)
    (((continuous_coverSourceCenter a.cover).comp continuous_fst).add continuous_snd)
    a.open_E (fun t _ ↦ by simpa only [add_zero] using (show coverSourceCenter a.cover t ∈ a.E from a.centers_E (a.cover.center t).property))
  refine ⟨r/2,by positivity,?_⟩
  intro t x hx
  have h := hri t (mem_univ t) (x-coverSourceCenter a.cover t) (by linarith)
  simpa using h

theorem original_logarithmic_jet_estimates (L : ℝ) (hL : 0 < L) :
    ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0, ∃ c > 0, ∃ C > 0,
      ∀ᶠ n : ℕ in atTop, ∀ t x,
      ‖x-coverSourceCenter a.cover t.1‖ ≤ L*(n:ℝ)^(-1/2:ℝ) →
      ‖a.beams.amplitude n t x-1‖ ≤ Ca*(n:ℝ)^(-1/2:ℝ) ∧
      (1/2:ℝ) ≤ ‖a.beams.amplitude n t x‖ ∧ ‖a.beams.amplitude n t x‖ ≤ 3/2 ∧
      a.beams.wave n t x ≠ 0 ∧
      (c ≤ ‖a.beams.wave n t x‖*Real.exp (-(n:ℝ)*S x) ∧
        ‖a.beams.wave n t x‖*Real.exp (-(n:ℝ)*S x) ≤ C) ∧
      ∀ v,
      |(normalizedLogJet n (a.beams.wave n t) x v).re -
        (fderiv ℝ S x v-a.originalEta t*g (coverSourceCenter a.cover t.1) (x-coverSourceCenter a.cover t.1) v)| ≤ Cr/n*‖v‖ ∧
      |(normalizedLogJet n (a.beams.wave n t) x v).im -
        g (coverSourceCenter a.cover t.1) (a.cover.triple.q t.1 t.2) v| ≤ Ci*(n:ℝ)^(-1/2:ℝ)*‖v‖ := by
  have hy := continuous_coverSourceCenter a.cover
  have hp0 (t : a.cover.Parameter) := a.nonzero_gradient _ (a.cover.center t).property
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,hjet⟩ := a.beams.uniform_logarithmic_jet_estimates
    a.smooth_G a.symmetric_G a.positive_G a.smooth_A hy hp0 L hL
  obtain ⟨c,hc,C,hC,hscalar⟩ := a.beams.uniform_relative_wave_bounds
    a.smooth_G a.positive_G a.smooth_A hy hp0 L hL
  obtain ⟨r,hr,hri⟩ := a.common_original_neighborhood
  refine ⟨Ca,hCa,Cr,hCr,Ci,hCi,c,hc,C,hC,?_⟩
  filter_upwards [eventually_nat_frequency hjet,eventually_nat_frequency hscalar,
    eventually_nat_frequency (half_scale_eventually L 1 r hr)] with n hj hs hn
  intro t x hx
  have hxE := hri t.1 x (hx.trans hn.2.1)
  obtain ⟨_,_,hA⟩ := a.germ x hxE
  obtain ⟨ha,hl,hu,hne,hrest⟩ := hj t x hx
  have hsc := hs t x hx
  rw [hA.self_of_nhds] at hsc
  refine ⟨ha,hl,hu,hne,hsc,?_⟩
  intro v
  have hh := hrest v
  rw [hA.fderiv_eq,a.eta_original,(a.center_identifications t.1).1] at hh
  exact hh

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeLogJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_logarithmic_jet_estimates_oai (hUD : U ⊆ D) (L : ℝ) (hL : 0 < L) :
    ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0, ∃ c > 0, ∃ C > 0,
      ∀ᶠ n : ℕ in atTop, ∀ (z : SourceGrid U n) (j : Fin 3) (x : _root_.OAI.Yau.Jets.Coord),
      ‖x-scaledLatticePoint n z‖ ≤ L*(n:ℝ)^(-1/2:ℝ) →
      let t := (latticeFrame a.cover hUD n z,j)
      let V := latticeWave a.cover a.beams hUD n z j
      ‖a.beams.amplitude n t x-1‖ ≤ Ca*(n:ℝ)^(-1/2:ℝ) ∧
      (1/2:ℝ) ≤ ‖a.beams.amplitude n t x‖ ∧ ‖a.beams.amplitude n t x‖ ≤ 3/2 ∧ V x ≠ 0 ∧
      (c ≤ ‖V x‖*Real.exp (-(n:ℝ)*S x) ∧ ‖V x‖*Real.exp (-(n:ℝ)*S x) ≤ C) ∧
      ∀ v,
      |(normalizedLogJet n V x v).re -
        (fderiv ℝ S x v-a.latticeEta hUD n z j*g (scaledLatticePoint n z) (x-scaledLatticePoint n z) v)| ≤ Cr/n*‖v‖ ∧
      |(normalizedLogJet n V x v).im - g (scaledLatticePoint n z) (a.cover.triple.q t.1 t.2) v| ≤
        Ci*(n:ℝ)^(-1/2:ℝ)*‖v‖ := by
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,c,hc,C,hC,hb⟩ := a.original_logarithmic_jet_estimates L hL
  refine ⟨Ca,hCa,Cr,hCr,Ci,hCi,c,hc,C,hC,?_⟩
  filter_upwards [hb] with n hn
  intro z j x hx
  have hx' : ‖x-coverSourceCenter a.cover (latticeFrame a.cover hUD n z)‖ ≤ L*(n:ℝ)^(-1/2:ℝ) := by
    simpa only [latticeFrame_center] using hx
  simpa only [latticeWave,TripleSourceWaveData.wave,latticeEta,latticeFrame_center] using
    hn (latticeFrame a.cover hUD n z,j) x hx'

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates_oai := @OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates_oai
