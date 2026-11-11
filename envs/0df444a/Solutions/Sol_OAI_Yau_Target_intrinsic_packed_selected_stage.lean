-- Prove2me | solution 1 for OAI.Yau.Target.intrinsic_packed_selected_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:32:36.14762+00:00
-- url     : https://prove2.me/submissions/f68229de-489b-4edd-be3e-c415e650cb70

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_lattice_good_event_probability
import Theorems.Thm_OAI_Yau_Geometry_lattice_physical_sign_subballs_fixed_domain
import Theorems.Thm_OAI_Yau_Target_intrinsic_noncritical_placed_data
import Theorems.Thm_OAI_Yau_Target_intrinsic_placed_total_residual

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

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricCoercivity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

lemma uniform_metric_coercivity (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hp : ∀ t v, v ≠ 0 → 0 < g t v v) :
    ∃ c > 0, ∃ B > 0, ∀ t, ‖g t‖ ≤ B ∧ ∀ v, c*‖v‖^2 ≤ g t v v := by
  have hc : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ g z.1 z.2 z.2) :=
    ((hg.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨c,hc0,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0:_root_.OAI.Yau.Jets.Coord) 1)) _ hc.continuousOn
    (fun z hz ↦ hp z.1 z.2 (by intro he; simpa [he] using hz.2))
  obtain ⟨B,hB,hBb⟩ := (isCompact_univ.image hg).isBounded.exists_pos_norm_le
  refine ⟨c,hc0,B,hB,?_⟩
  intro t
  refine ⟨hBb _ ⟨t,mem_univ _,rfl⟩,?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hh := (hbound (t,(‖v‖⁻¹:ℝ) • v)
    ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have he : ‖v‖^2*(‖v‖⁻¹*(‖v‖⁻¹*g t v v)) = g t v v := by field_simp
  rw [he] at hmul
  nlinarith

end
end Yau.Geometry

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

lemma metricGradient_continuous (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (metricGradient g S) :=
  (positive_metric_inverse_continuous g hg.continuous hp).clm_apply
    (hS.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSmoothExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem compact_smooth_extension {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : _root_.OAI.Yau.Jets.Coord → F) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : _root_.OAI.Yau.Jets.Coord → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ U ∧
      ∀ x ∈ K, G =ᶠ[𝓝 x] f := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  let G := fun x ↦ b x • f x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact hb.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hbU hx)))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  have hsupp : tsupport G ⊆ tsupport b := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [G,hz])
  refine ⟨G,hG,hbc.of_isClosed_subset isClosed_closure hsupp,hsupp.trans hbU,?_⟩
  intro x hx
  filter_upwards [hb1 x hx] with z hz
  simp [G,hz]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LocalCovarianceGeometry
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

include a in
theorem original_covariance_geometry : ∃ mu > 0, ∃ B > 0, ∀ x ∈ D,
    ‖g x‖ ≤ B ∧ ‖fderiv ℝ S x‖ ≤ B ∧ ∀ v, mu*‖v‖^2 ≤ g x v v := by
  let y := coverSourceCenter a.cover
  have hy := continuous_coverSourceCenter a.cover
  obtain ⟨mu,hmu,B,hB,hg⟩ := uniform_metric_coercivity (a.G ∘ y)
    (a.smooth_G.continuous.comp hy) (fun t ↦ a.positive_G (y t))
  have hc : Continuous (fun t ↦ fderiv ℝ a.A (y t)) :=
    (a.smooth_A.continuous_fderiv (by simp)).comp hy
  obtain ⟨M,hM,hm⟩ := (isCompact_univ.image hc).isBounded.exists_pos_norm_le
  refine ⟨mu,hmu,B+M,by positivity,?_⟩
  intro x hx
  let t := selectFrame a.cover ⟨x,hx⟩
  have he : y t = x := selectFrame_center a.cover ⟨x,hx⟩
  have hG := hg t
  change ‖a.G (y t)‖ ≤ B ∧ ∀ v, mu*‖v‖^2 ≤ a.G (y t) v v at hG
  rw [he] at hG
  have hA := hm _ ⟨t,mem_univ _,rfl⟩
  change ‖fderiv ℝ a.A (y t)‖ ≤ M at hA
  rw [he] at hA
  obtain ⟨hge,_,hae⟩ := a.germ x (a.centers_E hx)
  rw [hge.self_of_nhds] at hG
  rw [hae.fderiv_eq] at hA
  exact ⟨hG.1.trans (by linarith),hA.trans (by linarith),hG.2⟩

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeEnergyLowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma compact_inner_ball {Q U : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) :
    ∃ r > 0, ∀ x ∈ Q, closedBall x r ⊆ U := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  obtain ⟨r,hr,hri⟩ := compact_family_common_radius isCompact_univ
    (fun z : Q × _root_.OAI.Yau.Jets.Coord ↦ (z.1:_root_.OAI.Yau.Jets.Coord)+z.2)
    ((continuous_subtype_val.comp continuous_fst).add continuous_snd)
    hU (fun t _ ↦ by simpa only [add_zero] using hQU t.property)
  refine ⟨r/2,by positivity,?_⟩
  intro x hx z hz
  have hn : ‖z-x‖ ≤ r/2 := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have h := hri ⟨x,hx⟩ (mem_univ _) (z-x) (by linarith)
  simpa using h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FiniteWaveDerivativeBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussianWaveField_contDiff (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (a : ι × Fin 2 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) : ContDiff ℝ ∞ (gaussianWaveField V a) := by
  classical
  exact Complex.reCLM.contDiff.comp (ContDiff.sum (fun i _ ↦ contDiff_const.mul (hV i)))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricFrequencyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma sourceEuclideanNorm_smul (r : ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    sourceEuclideanNorm (r • v) = |r| * sourceEuclideanNorm v := by
  simp only [sourceEuclideanNorm,Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq_eq_abs]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_BallGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

lemma sourceEuclideanNorm_eq_norm (x : _root_.OAI.Yau.Jets.Coord) :
    sourceEuclideanNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4))‖ := by
  simp only [EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs,sourceEuclideanNorm]

lemma sourceEuclideanNorm_add_le (x y : _root_.OAI.Yau.Jets.Coord) :
    sourceEuclideanNorm (x+y) ≤ sourceEuclideanNorm x+sourceEuclideanNorm y := by
  simp_rw [sourceEuclideanNorm_eq_norm]
  exact norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

lemma sourceEuclideanNorm_single (j : Fin 4) (t : ℝ) :
    sourceEuclideanNorm (t • Pi.single j (1:ℝ)) = |t| := by
  rw [sourceEuclideanNorm_smul]
  simp [sourceEuclideanNorm,Pi.single_apply]

lemma sourceEuclideanBall_convex (R : ℝ) : Convex ℝ {x : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm x ≤ R} := by
  intro x hx y hy a b ha hb hab
  change sourceEuclideanNorm (a • x+b • y) ≤ R
  apply (sourceEuclideanNorm_add_le _ _).trans
  rw [sourceEuclideanNorm_smul,sourceEuclideanNorm_smul,abs_of_nonneg ha,abs_of_nonneg hb]
  calc
    _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [← add_mul,hab,one_mul]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalMetricJetContinuityLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma linearMetricField_positive (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) :
    ∀ v, v ≠ 0 → 0 < linearMetricField e g x v v := by
  intro v hv
  exact hp (e v) (by intro h; exact hv (e.injective (h.trans e.map_zero.symm)))

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SphericalSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_rbd94f5_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedQuadratic_contDiff : ContDiff ℝ ∞ seedQuadratic :=
  seedZ1.contDiff.mul seedZ2.contDiff

lemma ambientComplexSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientComplexSeed N) :=
  seedQuadratic_contDiff.pow N

lemma ambientRealSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientRealSeed N) :=
  Complex.reCLM.contDiff.comp (ambientComplexSeed_contDiff N)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogarithmicBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff
noncomputable section

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_1_rbd94f5_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedLogDomain_open : IsOpen seedLogDomain :=
  Complex.isOpen_slitPlane.preimage seedQuadratic_contDiff.continuous

lemma seedLog_contDiffAt {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedLog x :=
  ((Complex.contDiffAt_log hx (n := ∞)).restrict_scalars ℝ).comp x seedQuadratic_contDiff.contDiffAt

lemma ambientSeed_exp_log (N : ℕ) {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    ambientComplexSeed N x = Complex.exp ((N:ℂ)*seedLog x) := by
  rw [Complex.exp_nat_mul,seedLog,Complex.exp_log (Complex.slitPlane_ne_zero hx)]
  rfl

lemma ambientSeed_log_trigonometric (N : ℕ) {x : SeedAmbient} (hx : x ∈ seedLogDomain) :
    ambientRealSeed N x = Real.exp ((N:ℝ)*seedLogReal x) * Real.cos ((N:ℝ)*seedLogImag x) := by
  rw [ambientRealSeed,ambientSeed_exp_log N hx,Complex.exp_re]
  simp [Complex.mul_re,Complex.mul_im,seedLogReal,seedLogImag]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedRoundPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

lemma seedChartAmbient_smooth : ContDiff ℝ ∞ seedChartAmbient := by
  rw [show seedChartAmbient = stereoInvFunAux (-(seedPoint : SeedAmbient)) ∘ centeredSphereIsometry seedPoint from
    centeredSphereChart_inverse seedPoint]
  exact contDiff_stereoInvFunAux.comp (centeredSphereIsometry seedPoint).contDiff

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientMetricJets
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

lemma coefficientMetricValue_smoothAt (c : CoefficientPoint E)
    (e : (E →L[ℝ] ℝ) ≃L[ℝ] E) (he : e.toContinuousLinearMap = c.1) :
    ContDiffAt ℝ ∞ (coefficientMetricValue : CoefficientPoint E → E →L[ℝ] E →L[ℝ] ℝ) c := by
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse c.1 := by
    rw [← he]; exact contDiffAt_map_inverse e
  exact contDiffAt_snd.smul (hi.comp c contDiffAt_fst)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PositiveContravariant
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coefficientMetric_positive (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α)) (hρ : 0 < c.2) (v : E) (hv : v ≠ 0) :
    0 < coefficientMetricValue c v v := by
  let e := positiveContravariantEquiv c.1 hp
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have he : e.symm v ≠ 0 := by
    intro hz
    have h := congrArg e hz
    exact hv (by simpa using h)
  have hh := hp (e.symm v) he
  change 0 < e.symm v (e (e.symm v)) at hh
  rw [e.apply_symm_apply] at hh
  simpa [coefficientMetricValue,hi] using mul_pos hρ hh

lemma coefficientMetric_symmetric (c : CoefficientPoint E)
    (hp : ∀ α : E →L[ℝ] ℝ, α ≠ 0 → 0 < α (c.1 α))
    (hs : ∀ α β : E →L[ℝ] ℝ, α (c.1 β) = β (c.1 α)) (u v : E) :
    coefficientMetricValue c u v = coefficientMetricValue c v u := by
  let e := positiveContravariantEquiv c.1 hp
  have hi : ContinuousLinearMap.inverse c.1 = e.symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv e
  have hh := hs (e.symm u) (e.symm v)
  change e.symm u (e (e.symm v)) = e.symm v (e (e.symm u)) at hh
  rw [e.apply_symm_apply,e.apply_symm_apply] at hh
  simpa [coefficientMetricValue,hi] using congrArg (fun z : ℝ ↦ c.2*z) hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma seedRealChart_smoothAt {y : BaseModel} (hy : seedChartAmbient y ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedRealChart y := by
  exact (Complex.reCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt hy)).comp y
    seedChartAmbient_smooth.contDiffAt

lemma seedImagChart_smoothAt {y : BaseModel} (hy : seedChartAmbient y ∈ seedLogDomain) :
    ContDiffAt ℝ ∞ seedImagChart y := by
  exact (Complex.imCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt hy)).comp y
    seedChartAmbient_smooth.contDiffAt

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SeedCoordMetricRegularity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma seedCoordMetric_smooth (c : BaseModel → CoefficientPoint BaseModel)
    (hc : ContDiff ℝ ∞ c)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α)) :
    ContDiff ℝ ∞ (seedCoordMetric c) := by
  have hm : ContDiff ℝ ∞ (coefficientMetricValue ∘ c) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (coefficientMetricValue_smoothAt (c y) (positiveContravariantEquiv (c y).1 (hp y)) rfl).comp y hc.contDiffAt
  have hh := (contDiff_const (c := seedCoordEquiv.toContinuousLinearMap.precomp ℝ)).clm_comp
    ((hm.comp seedCoordEquiv.contDiff).clm_comp
      (contDiff_const (c := seedCoordEquiv.toContinuousLinearMap)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  ext u v
  rfl

lemma seedCoordMetric_positive (c : BaseModel → CoefficientPoint BaseModel)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α))
    (hρ : ∀ y, 0 < (c y).2) (x : _root_.OAI.Yau.Jets.Coord) (v : _root_.OAI.Yau.Jets.Coord) (hv : v ≠ 0) :
    0 < seedCoordMetric c x v v :=
  linearMetricField_positive seedCoordEquiv (coefficientMetricValue ∘ c) x
    (coefficientMetric_positive (c (seedCoordEquiv x)) (hp _) (hρ _)) v hv

lemma seedCoordMetric_symmetric (c : BaseModel → CoefficientPoint BaseModel)
    (hp : ∀ y (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c y).1 α))
    (hs : ∀ y (α β : BaseModel →L[ℝ] ℝ), α ((c y).1 β) = β ((c y).1 α))
    (x u v : _root_.OAI.Yau.Jets.Coord) : seedCoordMetric c x u v = seedCoordMetric c x v u :=
  coefficientMetric_symmetric (c (seedCoordEquiv x)) (hp _) (hs _) _ _

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MatrixCoefficientMap
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix Yau.Geometry
open scoped RealInnerProductSpace ContDiff
noncomputable section

lemma baseCovectorCoordinates_apply (α : BaseModel →L[ℝ] ℝ) (v : BaseModel) :
    α v = baseCovectorCoordinates α ⬝ᵥ WithLp.ofLp v := by
  have hv := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  conv_lhs => rw [← hv]
  simp [baseCovectorCoordinates,map_sum,map_smul,dotProduct,mul_comm]

lemma baseCovectorCoordinates_injective : Function.Injective baseCovectorCoordinates := by
  intro α β h
  ext v
  rw [baseCovectorCoordinates_apply,baseCovectorCoordinates_apply,h]

lemma baseCovectorCoordinates_ne_zero {α : BaseModel →L[ℝ] ℝ} (hα : α ≠ 0) :
    baseCovectorCoordinates α ≠ 0 := by
  intro h
  exact hα (baseCovectorCoordinates_injective (h.trans (by ext i; rfl)))

lemma matrixContravariant_coordinates (A : Matrix (Fin 4) (Fin 4) ℝ)
    (α : BaseModel →L[ℝ] ℝ) :
    WithLp.ofLp (matrixContravariant A α) = A *ᵥ baseCovectorCoordinates α := by
  ext k
  simp [matrixContravariant,baseCovectorCoordinates,mulVec,dotProduct,
    EuclideanSpace.basisFun_apply,Pi.single_apply,ite_mul,mul_ite,mul_comm]

lemma matrixContravariant_pair (A : Matrix (Fin 4) (Fin 4) ℝ) (α β : BaseModel →L[ℝ] ℝ) :
    α (matrixContravariant A β) = baseCovectorCoordinates α ⬝ᵥ (A *ᵥ baseCovectorCoordinates β) := by
  rw [baseCovectorCoordinates_apply,matrixContravariant_coordinates]

lemma matrixContravariant_positive (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosDef)
    (α : BaseModel →L[ℝ] ℝ) (hα : α ≠ 0) : 0 < α (matrixContravariant A α) := by
  rw [matrixContravariant_pair]
  simpa only [star_trivial] using hA.dotProduct_mulVec_pos (baseCovectorCoordinates_ne_zero hα)

lemma matrixCovariant_coordinates (B : Matrix (Fin 4) (Fin 4) ℝ) (v : BaseModel) :
    baseCovectorCoordinates (matrixCovariant B v) = B *ᵥ WithLp.ofLp v := by
  ext k
  simp [baseCovectorCoordinates,matrixCovariant,
    EuclideanSpace.inner_single_left,mulVec,dotProduct,mul_comm]

lemma matrixCovariant_apply (B : Matrix (Fin 4) (Fin 4) ℝ) (v w : BaseModel) :
    matrixCovariant B v w = (B *ᵥ WithLp.ofLp v) ⬝ᵥ WithLp.ofLp w := by
  rw [baseCovectorCoordinates_apply,matrixCovariant_coordinates]

lemma matrixContravariant_inverse (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsUnit A.det) :
    ContinuousLinearMap.inverse (matrixContravariant A) = matrixCovariant A⁻¹ := by
  apply ContinuousLinearMap.inverse_eq
  · ext v i
    change (matrixContravariant A (matrixCovariant A⁻¹ v)) i = v i
    have h := matrixContravariant_coordinates A (matrixCovariant A⁻¹ v)
    rw [matrixCovariant_coordinates,mulVec_mulVec,mul_nonsing_inv A hA,one_mulVec] at h
    exact congrFun h i
  · ext α v
    have h : baseCovectorCoordinates (matrixCovariant A⁻¹ (matrixContravariant A α)) =
        baseCovectorCoordinates α := by
      rw [matrixCovariant_coordinates,matrixContravariant_coordinates,mulVec_mulVec,
        nonsing_inv_mul A hA,one_mulVec]
    exact congrArg (fun β : BaseModel →L[ℝ] ℝ ↦ β v) (baseCovectorCoordinates_injective h)

lemma matrixCovariant_smul (r : ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixCovariant (r • B) = r • matrixCovariant B := by
  ext v w
  simp [matrixCovariant_apply,smul_mulVec,smul_dotProduct]

lemma coefficientMetric_matrix (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosDef) (ρ : ℝ) :
    coefficientMetricValue (matrixContravariant A,ρ) = matrixCovariant (ρ • A⁻¹) := by
  rw [coefficientMetricValue,matrixContravariant_inverse A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    matrixCovariant_smul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientMap
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsicChartCoefficient_pair (A : IntrinsicTensor) (ρ : Base → ℝ)
    (p : Base) (z : BaseModel) (α β : BaseModel →L[ℝ] ℝ) :
    α ((intrinsicChartCoefficient A ρ p z).1 β) =
      A ((extChartAt (𝓡 4) p).symm z)
        (sphereCoordinateCovector p z (baseCovectorCoordinates α))
        (sphereCoordinateCovector p z (baseCovectorCoordinates β)) := by
  change α (matrixContravariant _ β) = _
  rw [matrixContravariant_pair,intrinsicSphereChartTensor_eq,intrinsicAmbientMatrix_chart_pairing]

variable (A : IntrinsicTensor) (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)

include hs hp in
lemma intrinsicSphereChartTensor_posDef (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) : (intrinsicSphereChartTensor A p z).PosDef := by
  rw [intrinsicSphereChartTensor_eq]
  change (frameContravariant _ _).PosDef
  rw [sphereChart_contravariant _ (intrinsicAmbientMatrix_posDef A hs hp _) zero_lt_one p hz
    (intrinsicAmbientMatrix_radial A _),one_smul]
  exact (sphereWeightedChartMatrix_posDef _ (intrinsicAmbientMatrix_posDef A hs hp _)
    zero_lt_one p hz).inv

include hs hp in
lemma intrinsicChartCoefficient_positive (ρ : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (α : BaseModel →L[ℝ] ℝ) (hα : α ≠ 0) :
    0 < α ((intrinsicChartCoefficient A ρ p z).1 α) :=
  matrixContravariant_positive _ (intrinsicSphereChartTensor_posDef A hs hp p hz) α hα

include hs in
lemma intrinsicChartCoefficient_symmetric (ρ : Base → ℝ) (p : Base) (z : BaseModel)
    (α β : BaseModel →L[ℝ] ℝ) :
    α ((intrinsicChartCoefficient A ρ p z).1 β) = β ((intrinsicChartCoefficient A ρ p z).1 α) := by
  rw [intrinsicChartCoefficient_pair,intrinsicChartCoefficient_pair,hs]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientMetric
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section

variable (A : IntrinsicTensor) (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (ρ : Base → ℝ) (hρ : ∀ x, 0 < ρ x)

include hs hp hρ in
lemma intrinsicChartCoefficient_metric (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    coefficientMetricValue (intrinsicChartCoefficient A ρ p z) =
      matrixCovariant (baseChartMetric (intrinsicAmbientMatrix A) ρ p z) := by
  let B := intrinsicSphereChartTensor A p z
  let G := baseChartMetric (intrinsicAmbientMatrix A) ρ p z
  let r := ρ ((extChartAt (𝓡 4) p).symm z)
  have hr : 0 < r := hρ _
  have hB : B.PosDef := intrinsicSphereChartTensor_posDef A hs hp p hz
  have hG : G.PosDef := sphereWeightedChartMatrix_posDef _
    (intrinsicAmbientMatrix_posDef A hs hp _) hr p hz
  have hi : G⁻¹ = r⁻¹ • B := intrinsic_horizontal_inverse A hs hp ρ hρ p hz
  have hb : B = r • G⁻¹ := by rw [hi,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hbi : B⁻¹ = r⁻¹ • G := by
    apply Matrix.inv_eq_left_inv
    rw [hb,smul_mul_assoc,mul_smul_comm,smul_smul,inv_mul_cancel₀ hr.ne',one_smul,
      mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne')]
  change coefficientMetricValue (matrixContravariant B,r) = matrixCovariant G
  rw [coefficientMetric_matrix B hB r,hbi,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCoefficientSmooth
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)

include hA hs hp in
lemma intrinsicChartCoefficient_smoothAt (ρ : Base → ℝ)
    (hρ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target) :
    ContDiffAt ℝ ∞ (intrinsicChartCoefficient A ρ p) z := by
  apply ContDiffAt.prodMk _ (smooth_inverse_chart_comp ρ hρ p hz)
  change ContDiffAt ℝ ∞ (fun w ↦ matrixContravariant (intrinsicSphereChartTensor A p w)) z
  unfold matrixContravariant
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  let : IsBoundedSMul ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
    IsBoundedSMul.of_norm_smul_le ContinuousLinearMap.opNorm_smul_le
  exact (intrinsicSphereChartTensor_smoothAt A hA hs hp p hz i j).smul contDiffAt_const

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteBallPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open Set Metric
noncomputable section

lemma finite_fivefold_packing {E : Type*} [PseudoMetricSpace E]
    {Q : Set E} (hQ : IsCompact Q) (r : E → ℝ) (hr : ∀ x ∈ Q, 0 < r x) :
    ∃ t : Finset E, (↑t : Set E) ⊆ Q ∧
      (↑t : Set E).PairwiseDisjoint (fun x ↦ closedBall x (r x)) ∧
      Q ⊆ ⋃ x ∈ t, closedBall x (5*r x) := by
  classical
  obtain ⟨v,hvQ,hvfin,hcover⟩ := hQ.elim_finite_subcover_image
    (fun x (_ : x ∈ Q) ↦ isOpen_ball (x := x) (ε := r x))
    (show Q ⊆ ⋃ x ∈ Q, ball x (r x) from fun x hx ↦
      mem_iUnion₂.mpr ⟨x,hx,mem_ball_self (hr x hx)⟩)
  obtain ⟨R,hR⟩ := (hvfin.image r).bddAbove
  obtain ⟨u,huv,hdis,hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall v id r R
      (fun x hx ↦ hR (mem_image_of_mem r hx)) 5 (by norm_num)
  have hufin := hvfin.subset huv
  refine ⟨hufin.toFinset,by simpa using huv.trans hvQ,by simpa using hdis,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hx)
  obtain ⟨z,hz,hzcover⟩ := hcov y hy
  exact mem_iUnion₂.mpr ⟨z,hufin.mem_toFinset.mpr hz,hzcover (ball_subset_closedBall hxy)⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_BallPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric MeasureTheory
noncomputable section

lemma sourceClosedBall_preimage (x : _root_.OAI.Yau.Jets.Coord) (r : ℝ) :
    sourceClosedBall x r = (WithLp.toLp 2) ⁻¹'
      closedBall (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4)) r := by
  ext y
  simp only [sourceClosedBall,mem_ofPred_eq,mem_preimage,mem_closedBall,dist_eq_norm,
    sourceEuclideanNorm_eq_norm]
  rfl

lemma sourceClosedBall_isCompact (x : _root_.OAI.Yau.Jets.Coord) (r : ℝ) : IsCompact (sourceClosedBall x r) := by
  rw [sourceClosedBall_preimage]
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).toHomeomorph.symm
  exact e.isCompact_preimage.mpr (isCompact_closedBall _ _)

lemma sourceClosedBall_volume (x : _root_.OAI.Yau.Jets.Coord) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (sourceClosedBall x r) = (Real.pi^2/2)*r^4 := by
  rw [Measure.real,sourceClosedBall_preimage,
    (PiLp.volume_preserving_toLp (Fin 4)).measure_preimage measurableSet_closedBall.nullMeasurableSet,
    InnerProductSpace.volume_closedBall_of_dim_even (k := 2) (by simp)]
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (show 0 ≤ Real.pi^2/2 by positivity)]
  ring

lemma source_finite_fivefold_packing {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : _root_.OAI.Yau.Jets.Coord → ℝ) (hr : ∀ x ∈ Q, 0 < r x) :
    ∃ t : Finset _root_.OAI.Yau.Jets.Coord, (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ Q ∧
      (↑t : Set _root_.OAI.Yau.Jets.Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (r x)) ∧
      Q ⊆ ⋃ x ∈ t, sourceClosedBall x (5*r x) := by
  classical
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).toHomeomorph.symm
  obtain ⟨t,htQ,htdis,htcov⟩ := finite_fivefold_packing (hQ.image e.continuous)
    (fun x ↦ r (e.symm x)) (by rintro _ ⟨x,hx,rfl⟩; simpa using hr x hx)
  refine ⟨t.image e.symm,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,hzy⟩ := htQ hy
    simpa [← hzy] using hz
  · intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h ↦ hxy (congrArg e.symm h)
    have hd := htdis ha hb hab
    apply Disjoint.preimage e hd |>.mono
    · intro z hz
      change dist (e z) a ≤ r (e.symm a)
      change ‖e z-a‖ ≤ _
      dsimp only at hz
      rw [sourceClosedBall_preimage] at hz
      exact hz
    · intro z hz
      change dist (e z) b ≤ r (e.symm b)
      change ‖e z-b‖ ≤ _
      dsimp only at hz
      rw [sourceClosedBall_preimage] at hz
      exact hz
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (htcov (mem_image_of_mem e hx))
    refine mem_iUnion₂.mpr ⟨e.symm y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
    change sourceEuclideanNorm (x-e.symm y) ≤ _
    rw [sourceEuclideanNorm_eq_norm]
    exact hxy

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CertificateSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem bad_event_integral_bound {Z : Ω → ℝ} {Q : Set Ω} {T : ℝ}
    (hZ : Integrable Z μ) (hbound : ∀ w, Z w ≤ T) :
    (∫ w in Qᶜ, Z w ∂μ) ≤ (μ Qᶜ).toReal * T := by
  have h := integral_mono hZ.integrableOn (integrable_const T :
    Integrable (fun _ : Ω ↦ T) (μ.restrict Qᶜ)) hbound
  simpa [Measure.real, smul_eq_mul] using h

theorem exists_good_certificate_weight {Z : Ω → ℝ} {Q : Set Ω} {T c : ℝ}
    (hZ : Integrable Z μ) (hQ : MeasurableSet Q)
    (hT : 0 < T) (hc : 0 < c) (hbound : ∀ w, Z w ≤ T)
    (hexpect : c * T ≤ ∫ w, Z w ∂μ) (hfail : (μ Qᶜ).toReal < c / 2) :
    ∃ w ∈ Q, c * T / 2 ≤ Z w := by
  have hbad := bad_event_integral_bound (Q := Q) hZ hbound
  have hsplit := integral_add_compl hQ hZ
  have hgood : c * T / 2 < ∫ w in Q, Z w ∂μ := by
    have hm := mul_lt_mul_of_pos_right hfail hT
    nlinarith
  by_contra hn
  push Not at hn
  have hp : ∀ w, Q.indicator Z w ≤ c * T / 2 := by
    intro w
    by_cases hw : w ∈ Q
    · simpa [hw] using (hn w hw).le
    · simp only [indicator_of_notMem hw]
      positivity
  have hupper := integral_mono (hZ.indicator hQ)
    (integrable_const (c * T / 2) : Integrable (fun _ : Ω ↦ c * T / 2) μ) hp
  rw [integral_indicator hQ] at hupper
  have hupper' : (∫ w in Q, Z w ∂μ) ≤ c * T / 2 := by simpa using hupper
  exact (not_lt_of_ge hupper') hgood

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_NodalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem zero_on_segment {u : E → ℝ} (hu : Continuous u) {a b : E}
    (ha : u a < 0) (hb : 0 < u b) :
    ∃ t ∈ Icc (0 : ℝ) 1, u (segmentPoint a b t) = 0 := by
  have hc : Continuous (fun t : ℝ ↦ u (segmentPoint a b t)) :=
    hu.comp (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const))
  have h0 : (0 : ℝ) ∈ Icc (u (segmentPoint a b 0)) (u (segmentPoint a b 1)) := by
    simpa [segmentPoint] using And.intro ha.le hb.le
  exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn h0

theorem projection_covers {u : E → ℝ} (hu : Continuous u)
    (P : E →L[ℝ] F) (L : F →L[ℝ] E) (hL : ∀ z, P (L z) = z)
    {a b : E} (ha : P a = 0) (hb : P b = 0) {A : Set F} {C : Set E}
    (hneg : ∀ z ∈ A, u (a + L z) < 0)
    (hpos : ∀ z ∈ A, 0 < u (b + L z))
    (hseg : ∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
      segmentPoint (a + L z) (b + L z) t ∈ C) :
    A ⊆ P '' (C ∩ {x | u x = 0}) := by
  intro z hz
  obtain ⟨t, ht, hzero⟩ := zero_on_segment hu (hneg z hz) (hpos z hz)
  refine ⟨segmentPoint (a + L z) (b + L z) t, ⟨hseg z hz t ht, hzero⟩, ?_⟩
  simp only [segmentPoint, map_add, map_smul, ha, hb, hL, zero_add]
  module

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinateTransverseDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma transverseProjection_inclusion (j : Fin 4) (z : TransverseCoord) :
    transverseProjection j (transverseInclusion j z) = z := by
  ext k
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 4 ↦ ℝ) j 0 z k

lemma transverseProjection_axis (j : Fin 4) (a : ℝ) :
    transverseProjection j (a • Pi.single j 1) = 0 := by
  ext k
  simp [transverseProjection,Fin.succAbove_ne]

lemma transverseInclusion_sourceNorm (j : Fin 4) (z : TransverseCoord) :
    sourceEuclideanNorm (transverseInclusion j z) = Real.sqrt (∑ k : Fin 3, (z k)^2) := by
  unfold sourceEuclideanNorm
  rw [Fin.sum_univ_succAbove _ j]
  simp [transverseInclusion]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteCertificateWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
lemma successfulTestWeight_bounds (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (A : ι → Set Ω) (a : Ω) :
    0 ≤ successfulTestWeight w A a ∧ successfulTestWeight w A a ≤ ∑ i, w i := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact indicator_nonneg (fun _ _ ↦ hw i) a
  · apply Finset.sum_le_sum
    intro i _
    by_cases h : a ∈ A i <;> simp [h,hw i]

lemma successfulTestWeight_integrable (w : ι → ℝ) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) : Integrable (successfulTestWeight w A) μ := by
  unfold successfulTestWeight
  exact integrable_finsetSum _ (fun i _ ↦ (integrable_const (w i)).indicator (hA i))

lemma successfulTestWeight_integral (w : ι → ℝ) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) :
    (∫ a, successfulTestWeight w A a ∂μ) = ∑ i, μ.real (A i)*w i := by
  unfold successfulTestWeight
  rw [integral_finsetSum _ (fun i _ ↦ (integrable_const (w i)).indicator (hA i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hA i),setIntegral_const,smul_eq_mul]

lemma exists_good_successful_test_weight (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hT : 0 < ∑ i, w i) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {c : ℝ} (hc : 0 < c) (hprob : ∀ i, c ≤ μ.real (A i))
    (Q : Set Ω) (hQ : MeasurableSet Q) (hfail : (μ Qᶜ).toReal < c/2) :
    ∃ a ∈ Q, c*(∑ i, w i)/2 ≤ successfulTestWeight w A a := by
  apply exists_good_certificate_weight (successfulTestWeight_integrable w A hA) hQ hT hc
    (fun a ↦ (successfulTestWeight_bounds w hw A a).2) _ hfail
  rw [successfulTestWeight_integral w A hA,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (hprob i) (hw i))

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteCoverIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open Set MeasureTheory
noncomputable section

lemma integral_le_finite_cover {E ι : Type*} [MeasurableSpace E]
    {μ : Measure E} {Q : Set E} (hQ : MeasurableSet Q) {s : E → ℝ}
    (hs : IntegrableOn s Q μ) (t : Finset ι) (B : ι → Set E) (c : ι → ℝ)
    (hB : ∀ i ∈ t, MeasurableSet (B i)) (hfin : ∀ i ∈ t, μ (B i) ≠ ⊤)
    (hc : ∀ i ∈ t, 0 ≤ c i) (hcov : Q ⊆ ⋃ i ∈ t, B i)
    (hbound : ∀ i ∈ t, ∀ x ∈ Q ∩ B i, s x ≤ c i) :
    (∫ x in Q, s x ∂μ) ≤ ∑ i ∈ t, μ.real (B i)*c i := by
  classical
  have hi : ∀ i ∈ t, Integrable ((B i).indicator (fun _ ↦ c i)) μ := by
    intro i hit
    exact (integrable_indicator_iff (hB i hit)).mpr (integrableOn_const (hfin i hit))
  have hm : ∀ x, Q.indicator s x ≤ ∑ i ∈ t, (B i).indicator (fun _ ↦ c i) x := by
    intro x
    have hn : ∀ i ∈ t, 0 ≤ (B i).indicator (fun _ ↦ c i) x :=
      fun i hit ↦ indicator_nonneg (fun _ _ ↦ hc i hit) x
    by_cases hx : x ∈ Q
    · obtain ⟨i,hit,hxi⟩ := mem_iUnion₂.mp (hcov hx)
      rw [indicator_of_mem hx]
      apply (hbound i hit x ⟨hx,hxi⟩).trans
      calc
        c i = (B i).indicator (fun _ ↦ c i) x := (indicator_of_mem hxi (fun _ ↦ c i)).symm
        _ ≤ _ := Finset.single_le_sum hn hit
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg hn
  have hh := integral_mono ((integrable_indicator_iff hQ).mpr hs)
    (integrable_finsetSum t hi) hm
  rw [integral_indicator hQ,integral_finsetSum t hi] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro i hit
  rw [integral_indicator (hB i hit),setIntegral_const,smul_eq_mul]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PackingVolumeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
noncomputable section

lemma packing_volume_weight {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q)
    {s : _root_.OAI.Yau.Jets.Coord → ℝ} (hs : ContinuousOn s Q) (t : Finset _root_.OAI.Yau.Jets.Coord) (r : _root_.OAI.Yau.Jets.Coord → ℝ)
    {N : ℝ} (hN : 0 ≤ N) (ht : (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ Q)
    (hr : ∀ x ∈ t, 0 ≤ r x) (hspos : ∀ x ∈ Q, 0 ≤ s x)
    (hscale : ∀ x ∈ t, N*s x*r x = 1)
    (hcov : Q ⊆ ⋃ x ∈ t, sourceClosedBall x (5*r x))
    (hcomp : ∀ x ∈ t, ∀ y ∈ Q ∩ sourceClosedBall x (5*r x), s y ≤ 2*s x) :
    N*(∫ x in Q, s x) ≤ 2*(Real.pi^2/2)*5^4 * ∑ x ∈ t, r x^3 := by
  have hh := integral_le_finite_cover (μ := volume) hQ.measurableSet (hs.integrableOn_compact hQ)
    t (fun x ↦ sourceClosedBall x (5*r x)) (fun x ↦ 2*s x)
    (fun x _ ↦ (sourceClosedBall_isCompact x _).measurableSet)
    (fun x _ ↦ (sourceClosedBall_isCompact x _).measure_ne_top)
    (fun x hx ↦ mul_nonneg (by norm_num) (hspos x (ht hx))) hcov hcomp
  apply (mul_le_mul_of_nonneg_left hh hN).trans
  rw [Finset.mul_sum,Finset.mul_sum]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro x hx
  rw [sourceClosedBall_volume x (mul_nonneg (by norm_num) (hr x hx))]
  calc
    N * (Real.pi^2/2*(5*r x)^4*(2*s x)) =
        (2*(Real.pi^2/2)*5^4*r x^3)*(N*s x*r x) := by ring
    _ = _ := by rw [hscale x hx,mul_one]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SignScaleSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma sourceSignScale_ge_two {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {S : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord} (hp : 0 ≤ g x (metricGradient g S x) (metricGradient g S x)) :
    2 ≤ sourceSignScale g S x := by
  unfold sourceSignScale
  apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
  nlinarith

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

include a in
lemma source_sign_scale_lower : ∀ x ∈ D, 2 ≤ sourceSignScale g S x := by
  obtain ⟨μ,hμ,B,hB,hgeom⟩ := a.original_covariance_geometry
  intro x hx
  exact sourceSignScale_ge_two ((by positivity : 0 ≤ μ*‖metricGradient g S x‖^2).trans
    ((hgeom x hx).2.2 _))

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SignScaleContinuity
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

lemma sourceSignScale_continuous (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (sourceSignScale g S) := by
  have hgrad := metricGradient_continuous g hg hp S hS
  exact (((hg.continuous.clm_apply hgrad).clm_apply hgrad).add continuous_const).sqrt

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma source_sign_scale_eq (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ a.E) :
    sourceSignScale a.G a.A x = sourceSignScale g S x := by
  obtain ⟨hg,_,hS⟩ := a.germ x hx
  unfold sourceSignScale
  rw [hg.self_of_nhds,(metricGradient_eventuallyEq hg hS).self_of_nhds]

include a in
lemma source_sign_scale_continuousOn {H : Set _root_.OAI.Yau.Jets.Coord} (hHD : H ⊆ D) :
    ContinuousOn (sourceSignScale g S) H := by
  apply (sourceSignScale_continuous a.G a.smooth_G a.positive_G a.A a.smooth_A).continuousOn.congr
  intro x hx
  exact (a.source_sign_scale_eq x (a.centers_E (hHD hx))).symm

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SignScalePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section

lemma compact_sign_scale_dilates {Q U : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q)
    (hU : IsOpen U) (hQU : Q ⊆ U) (s : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hs : ContinuousOn s Q) (hlo : ∀ x ∈ Q, 2 ≤ s x) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ x ∈ Q,
      sourceClosedBall x (5/((n:ℝ)*s x)) ⊆ U ∧
      ∀ y ∈ Q ∩ sourceClosedBall x (5/((n:ℝ)*s x)), s y ≤ 2*s x := by
  obtain ⟨ρ,hρ,hinner⟩ := compact_inner_ball hQ hU hQU
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp
    (hQ.uniformContinuousOn_of_continuous hs) 1 (by norm_num)
  have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop)
  filter_upwards [ht.eventually (eventually_gt_atTop (5/ρ)),
    ht.eventually (eventually_gt_atTop (5/δ)),eventually_gt_atTop (0:ℕ)] with n hnρ hnδ hn
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  refine ⟨hn,?_⟩
  intro x hx
  have hsx : 0 < s x := by linarith [hlo x hx]
  have hrad : 5/((n:ℝ)*s x) < min ρ δ := by
    apply lt_min
    · apply (div_lt_iff₀ (mul_pos hn' hsx)).mpr
      have hh := (div_lt_iff₀ hρ).mp hnρ
      nlinarith [hlo x hx]
    · apply (div_lt_iff₀ (mul_pos hn' hsx)).mpr
      have hh := (div_lt_iff₀ hδ).mp hnδ
      nlinarith [hlo x hx]
  have hdist : ∀ y ∈ sourceClosedBall x (5/((n:ℝ)*s x)), dist y x ≤ 5/((n:ℝ)*s x) := by
    intro y hy
    exact (norm_le_sourceEuclideanNorm (y-x)).trans hy
  constructor
  · intro y hy
    apply hinner x hx
    exact (hdist y hy).trans (hrad.le.trans (min_le_left _ _))
  · intro y hy
    have hh := hd y hy.1 x hx ((hdist y hy.2).trans_lt (hrad.trans_le (min_le_right _ _)))
    rw [Real.dist_eq] at hh
    linarith [(abs_lt.mp hh).2,hlo x hx]

lemma compact_sign_scale_packing {Q U : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q)
    (hU : IsOpen U) (hQU : Q ⊆ U) (s : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hs : ContinuousOn s Q) (hlo : ∀ x ∈ Q, 2 ≤ s x) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ t : Finset _root_.OAI.Yau.Jets.Coord,
      let r := fun x ↦ ((n:ℝ)*s x)⁻¹
      (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ Q ∧
      (↑t : Set _root_.OAI.Yau.Jets.Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (r x)) ∧
      Q ⊆ ⋃ x ∈ t, sourceClosedBall x (5*r x) ∧
      (∀ x ∈ t, 0 < r x ∧ sourceClosedBall x (5*r x) ⊆ U) ∧
      (n:ℝ)*(∫ x in Q, s x) ≤ 2*(Real.pi^2/2)*5^4 * ∑ x ∈ t, r x^3 := by
  filter_upwards [compact_sign_scale_dilates hQ hU hQU s hs hlo] with n hn
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn.1
  let r := fun x ↦ ((n:ℝ)*s x)⁻¹
  have hr : ∀ x ∈ Q, 0 < r x := fun x hx ↦ inv_pos.mpr (mul_pos hn' (by linarith [hlo x hx]))
  obtain ⟨t,htQ,htdis,htcov⟩ := source_finite_fivefold_packing hQ r hr
  refine ⟨hn.1,t,htQ,htdis,htcov,?_,?_⟩
  · intro x hx
    refine ⟨hr x (htQ hx),?_⟩
    simpa only [r,div_eq_mul_inv] using (hn.2 x (htQ hx)).1
  · refine packing_volume_weight hQ hs t r hn'.le htQ
      (fun x hx ↦ (hr x (htQ hx)).le) (fun x hx ↦ by linarith [hlo x hx]) ?_ htcov ?_
    · intro x hx
      exact mul_inv_cancel₀ (mul_pos hn' (show 0 < s x by linarith [hlo x (htQ hx)])).ne'
    · intro x hx y hy
      apply (hn.2 x (htQ hx)).2 y
      simpa only [r,div_eq_mul_inv] using hy

namespace LocalCompactWaveData
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
  {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

lemma source_sign_scale_packing (a : LocalCompactWaveData g w S D m J K k0)
    {Q U : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) (hUD : U ⊆ D) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ t : Finset _root_.OAI.Yau.Jets.Coord,
      let r := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
      (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ Q ∧
      (↑t : Set _root_.OAI.Yau.Jets.Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (r x)) ∧
      Q ⊆ ⋃ x ∈ t, sourceClosedBall x (5*r x) ∧
      (∀ x ∈ t, 0 < r x ∧ sourceClosedBall x (5*r x) ⊆ U) ∧
      (n:ℝ)*(∫ x in Q, sourceSignScale g S x) ≤
        2*(Real.pi^2/2)*5^4 * ∑ x ∈ t, r x^3 :=
  compact_sign_scale_packing hQ hU hQU _ (a.source_sign_scale_continuousOn (hQU.trans hUD))
    (fun x hx ↦ a.source_sign_scale_lower x (hUD (hQU hx)))

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SignMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
noncomputable section

lemma compact_sign_mass_pos {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hvol : volume Q ≠ 0)
    (s : _root_.OAI.Yau.Jets.Coord → ℝ) (hs : ContinuousOn s Q) (hlo : ∀ x ∈ Q, 2 ≤ s x) :
    0 < ∫ x in Q, s x := by
  have hm : 0 < volume.real Q := ENNReal.toReal_pos hvol hQ.measure_ne_top
  have hh := setIntegral_mono_on (μ := volume)
    (integrableOn_const hQ.measure_ne_top : IntegrableOn (fun _ : _root_.OAI.Yau.Jets.Coord ↦ (2:ℝ)) Q)
    (hs.integrableOn_compact hQ) hQ.measurableSet hlo
  rw [setIntegral_const,smul_eq_mul] at hh
  linarith

namespace LocalCompactWaveData
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
  {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

lemma source_sign_mass_pos (a : LocalCompactWaveData g w S D m J K k0)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hvol : volume Q ≠ 0) (hQD : Q ⊆ D) :
    0 < ∫ x in Q, sourceSignScale g S x :=
  compact_sign_mass_pos hQ hvol _ (a.source_sign_scale_continuousOn hQD)
    (fun x hx ↦ a.source_sign_scale_lower x (hQD hx))

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransverseCylinderVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

lemma transverseCylinder_box_subset {r : ℝ} (hr : 0 ≤ r) :
    Icc (Fin.cons (-1:ℝ) (fun _ : Fin 3 ↦ -r/2))
      (Fin.cons (1:ℝ) (fun _ : Fin 3 ↦ r/2)) ⊆ transverseCylinder r := by
  intro z hz
  refine ⟨⟨by simpa using hz.1 0,by simpa using hz.2 0⟩,?_⟩
  have hz' (k : Fin 3) : -(r/2) ≤ z k.succ ∧ z k.succ ≤ r/2 := by
    constructor
    · simpa only [Fin.cons_succ,neg_div] using hz.1 k.succ
    · simpa using hz.2 k.succ
  change Real.sqrt (∑ k : Fin 3, (z k.succ)^2) ≤ r
  apply (Real.sqrt_le_left hr).mpr
  calc
    _ ≤ ∑ _ : Fin 3, (r/2)^2 := Finset.sum_le_sum (fun k _ ↦
      sq_le_sq' (hz' k).1 (hz' k).2)
    _ ≤ r^2 := by norm_num <;> nlinarith [sq_nonneg r]

lemma transverseCylinder_measure_lower {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (2*r^3) ≤ Measure.hausdorffMeasure (4:ℝ) (transverseCylinder r) := by
  have he : (Measure.hausdorffMeasure (4:ℝ) : Measure _root_.OAI.Yau.Jets.Coord) = volume := by
    simpa using (hausdorffMeasure_pi_real (ι := Fin 4))
  rw [he]
  have hvol : volume (Icc (Fin.cons (-1:ℝ) (fun _ : Fin 3 ↦ -r/2))
      (Fin.cons (1:ℝ) (fun _ : Fin 3 ↦ r/2)) : Set _root_.OAI.Yau.Jets.Coord) = ENNReal.ofReal (2*r^3) := by
    rw [Real.volume_Icc_pi,Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,show (1:ℝ)-(-1) = 2 by ring,
      show r/2- -r/2 = r by ring,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_pow hr]
  rw [← hvol]
  exact measure_mono (transverseCylinder_box_subset hr)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_PhysicalNodalDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
noncomputable section

lemma physical_sign_projection_covers (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : Continuous f)
    (x : _root_.OAI.Yau.Jets.Coord) (j : Fin 4) {R tau r : ℝ} (hR : 0 < R) (ht : 0 ≤ tau) (hr : 0 ≤ r)
    (htr : tau+r ≤ 1)
    (hpos : ∀ y ∈ sourceClosedBall x (r*R), 0 < f y)
    (hneg : ∀ y ∈ sourceClosedBall (x+R • (tau • Pi.single j 1)) (r*R), f y < 0) :
    transverseDisk (r*R) ⊆ (fun y ↦ transverseProjection j (y-x)) ''
      (sourceClosedBall x R ∩ {y | f y = 0}) := by
  let a : _root_.OAI.Yau.Jets.Coord := R • (tau • Pi.single j 1)
  have hL (z : TransverseCoord) (hz : z ∈ transverseDisk (r*R)) :
      sourceEuclideanNorm (transverseInclusion j z) ≤ r*R := by
    rw [transverseInclusion_sourceNorm]
    exact hz
  have hn (z : TransverseCoord) (hz : z ∈ transverseDisk (r*R)) :
      f (x+(a+transverseInclusion j z)) < 0 := by
    apply hneg
    change sourceEuclideanNorm ((x+(a+transverseInclusion j z))-(x+a)) ≤ r*R
    simpa only [add_sub_add_left_eq_sub,add_sub_cancel_left] using hL z hz
  have hp (z : TransverseCoord) (hz : z ∈ transverseDisk (r*R)) :
      0 < f (x+(0+transverseInclusion j z)) := by
    apply hpos
    change sourceEuclideanNorm ((x+(0+transverseInclusion j z))-x) ≤ r*R
    simpa only [zero_add,add_sub_cancel_left] using hL z hz
  have hseg (z : TransverseCoord) (hz : z ∈ transverseDisk (r*R)) :
      ∀ t ∈ Icc (0:ℝ) 1, segmentPoint (a+transverseInclusion j z) (0+transverseInclusion j z) t ∈
        {v : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm v ≤ R} := by
    intro t ht'
    have ha : sourceEuclideanNorm (a+transverseInclusion j z) ≤ R := by
      apply (sourceEuclideanNorm_add_le _ _).trans
      have hna : sourceEuclideanNorm a = R*tau := by
        dsimp [a]
        rw [smul_smul,sourceEuclideanNorm_single,abs_of_nonneg (mul_nonneg hR.le ht)]
      rw [hna]
      nlinarith [hL z hz]
    have hb : sourceEuclideanNorm (0+transverseInclusion j z) ≤ R := by
      rw [zero_add]
      apply (hL z hz).trans
      have hr1 : r ≤ 1 := le_trans (le_add_of_nonneg_left ht) htr
      simpa only [mul_one, mul_comm] using mul_le_mul (le_refl R) hr1 hr hR.le
    exact sourceEuclideanBall_convex R ha hb (by linarith [ht'.2] : 0 ≤ 1-t) ht'.1 (by ring)
  have hc := projection_covers (hf.comp (continuous_const.add continuous_id))
    (transverseProjection j) (transverseInclusion j) (transverseProjection_inclusion j)
    (show transverseProjection j a = 0 by dsimp [a]; rw [smul_smul]; exact transverseProjection_axis j _)
    (map_zero _) hn hp hseg
  intro z hz
  obtain ⟨v,⟨hv,hzero⟩,hproj⟩ := hc hz
  refine ⟨x+v,⟨?_,hzero⟩,?_⟩
  · change sourceEuclideanNorm (x+v-x) ≤ R
    simpa only [mem_ofPred_eq,add_sub_cancel_left] using hv
  · simpa only [add_sub_cancel_left] using hproj

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_PhysicalNodalCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

lemma cylinderProjection_lipschitz (x : _root_.OAI.Yau.Jets.Coord) (j : Fin 4) :
    LipschitzWith 1 (cylinderProjection x j) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [NNReal.coe_one,one_mul,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg dist_nonneg).mpr
  intro k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · change ‖y.2-z.2‖ ≤ dist y z
    rw [Prod.dist_eq]
    exact le_max_right _ _
  · have hh := (norm_le_pi_norm (y.1-z.1) (j.succAbove k)).trans
      (show ‖y.1-z.1‖ ≤ dist y z from by rw [Prod.dist_eq]; exact le_max_left _ _)
    simpa [cylinderProjection,transverseProjection,sub_sub_sub_cancel_right] using hh

lemma physical_sign_cylinder_covers (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : Continuous f)
    (x : _root_.OAI.Yau.Jets.Coord) (j : Fin 4) {R tau r : ℝ} (hR : 0 < R) (ht : 0 ≤ tau) (hr : 0 ≤ r)
    (htr : tau+r ≤ 1)
    (hpos : ∀ y ∈ sourceClosedBall x (r*R), 0 < f y)
    (hneg : ∀ y ∈ sourceClosedBall (x+R • (tau • Pi.single j 1)) (r*R), f y < 0) :
    transverseCylinder (r*R) ⊆ cylinderProjection x j ''
      ((sourceClosedBall x R ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | f y.1 = 0}) := by
  intro z hz
  obtain ⟨y,⟨hy,hzero⟩,hproj⟩ := physical_sign_projection_covers f hf x j hR ht hr htr hpos hneg hz.2
  refine ⟨(y,z 0),⟨⟨hy,hz.1⟩,hzero⟩,?_⟩
  change Fin.cons (z 0) (transverseProjection j (y-x)) = z
  dsimp only at hproj
  rw [hproj,Fin.cons_self_tail]

lemma physical_nodal_cylinder_measure (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : Continuous f)
    (x : _root_.OAI.Yau.Jets.Coord) (j : Fin 4) {R tau r : ℝ} (hR : 0 < R) (ht : 0 ≤ tau) (hr : 0 ≤ r)
    (htr : tau+r ≤ 1)
    (hpos : ∀ y ∈ sourceClosedBall x (r*R), 0 < f y)
    (hneg : ∀ y ∈ sourceClosedBall (x+R • (tau • Pi.single j 1)) (r*R), f y < 0) :
    ENNReal.ofReal (2*r^3*R^3) ≤ Measure.hausdorffMeasure (4:ℝ)
      ((sourceClosedBall x R ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | f y.1 = 0}) := by
  have hh := (transverseCylinder_measure_lower (mul_nonneg hr hR.le)).trans
    ((measure_mono (physical_sign_cylinder_covers f hf x j hR ht hr htr hpos hneg)).trans
      ((cylinderProjection_lipschitz x j).hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 4) _))
  simpa only [mul_pow,mul_assoc,ENNReal.coe_one,ENNReal.one_rpow,one_mul] using hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_FiniteNodalCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

lemma finite_nodal_cylinder_measure {ι : Type*} (t : Finset ι)
    (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : Continuous f) (x : ι → _root_.OAI.Yau.Jets.Coord) (R : ι → ℝ) (j : ι → Fin 4)
    {U : Set _root_.OAI.Yau.Jets.Coord} {tau r : ℝ} (ht : 0 ≤ tau) (hr : 0 ≤ r) (htr : tau+r ≤ 1)
    (hR : ∀ i ∈ t, 0 < R i)
    (hdis : (↑t : Set ι).PairwiseDisjoint (fun i ↦ sourceClosedBall (x i) (R i)))
    (hU : ∀ i ∈ t, sourceClosedBall (x i) (R i) ⊆ U)
    (hsign : ∀ i ∈ t,
      (∀ y ∈ sourceClosedBall (x i) (r*R i), 0 < f y) ∧
      (∀ y ∈ sourceClosedBall (x i+R i • (tau • Pi.single (j i) 1)) (r*R i), f y < 0)) :
    ENNReal.ofReal (2*r^3*∑ i ∈ t, (R i)^3) ≤
      Measure.hausdorffMeasure (4:ℝ) ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | f y.1 = 0}) := by
  classical
  let Z := fun i ↦ (sourceClosedBall (x i) (R i) ×ˢ Icc (-1:ℝ) 1) ∩
    {y : _root_.OAI.Yau.Jets.Coord × ℝ | f y.1 = 0}
  have hm (i : ι) : MeasurableSet (Z i) :=
    (((sourceClosedBall_isCompact (x i) (R i)).measurableSet.prod measurableSet_Icc).inter
      (isClosed_eq (hf.comp continuous_fst) continuous_const).measurableSet)
  have hd : (↑t : Set ι).PairwiseDisjoint Z := by
    intro i hi k hk hik
    apply disjoint_left.mpr
    intro y hyi hyk
    exact disjoint_left.mp (hdis hi hk hik) hyi.1.1 hyk.1.1
  have hsub : (⋃ i ∈ t, Z i) ⊆ (U ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | f y.1 = 0} := by
    intro y hy
    obtain ⟨i,hi,hyi⟩ := mem_iUnion₂.mp hy
    exact ⟨⟨hU i hi hyi.1.1,hyi.1.2⟩,hyi.2⟩
  calc
    _ = ∑ i ∈ t, ENNReal.ofReal (2*r^3*(R i)^3) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact mul_nonneg (by positivity) (pow_pos (hR i hi) 3).le
    _ ≤ ∑ i ∈ t, Measure.hausdorffMeasure (4:ℝ) (Z i) :=
      Finset.sum_le_sum (fun i hi ↦ physical_nodal_cylinder_measure f hf (x i) (j i)
        (hR i hi) ht hr htr (hsign i hi).1 (hsign i hi).2)
    _ = Measure.hausdorffMeasure (4:ℝ) (⋃ i ∈ t, Z i) :=
      (measure_biUnion_finset hd (fun i _ ↦ hm i)).symm
    _ ≤ _ := measure_mono hsub

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SuccessfulTestSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open Set MeasureTheory
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma exists_good_successful_tests (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hT : 0 < ∑ i, w i) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {c : ℝ} (hc : 0 < c) (hprob : ∀ i, c ≤ μ.real (A i))
    (Q : Set Ω) (hQ : MeasurableSet Q) (hfail : (μ Qᶜ).toReal < c/2) :
    ∃ a ∈ Q, ∃ u : Finset ι, (∀ i ∈ u, a ∈ A i) ∧
      c*(∑ i, w i)/2 ≤ ∑ i ∈ u, w i := by
  classical
  obtain ⟨a,ha,hweight⟩ := exists_good_successful_test_weight w hw hT A hA hc hprob Q hQ hfail
  refine ⟨a,ha,Finset.univ.filter (fun i ↦ a ∈ A i),?_,?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · convert hweight using 1
    all_goals try with_reducible_and_instances rfl
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a ∈ A i <;> simp [hi]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicSeedPatch
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma intrinsicSeedCoordMetric_eq (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (ρ : Base → ℝ) (hρ : ∀ x, 0 < ρ x) :
    seedCoordMetric (intrinsicChartCoefficient A ρ seedPoint) = intrinsicSeedCoordMetric A ρ := by
  funext x
  change linearMetricPull seedCoordEquiv _ = linearMetricPull seedCoordEquiv _
  rw [Function.comp_apply,intrinsicChartCoefficient_metric A hs hp ρ hρ seedPoint
    (by rw [centeredSphereChart_target]; trivial)]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedLogExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section

lemma seedCoordBranch_open : IsOpen seedCoordBranch :=
  seedLogDomain_open.preimage (seedChartAmbient_smooth.continuous.comp seedCoordEquiv.continuous)

lemma seedCoordReal_smoothOn : ContDiffOn ℝ ∞ seedCoordReal seedCoordBranch := by
  intro x hx
  exact ((seedRealChart_smoothAt hx).comp x seedCoordEquiv.contDiff.contDiffAt).contDiffWithinAt

lemma seedCoordImag_smoothOn : ContDiffOn ℝ ∞ seedCoordImag seedCoordBranch := by
  intro x hx
  exact ((seedImagChart_smoothAt hx).comp x seedCoordEquiv.contDiff.contDiffAt).contDiffWithinAt

theorem seed_log_compact_extensions {K : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K) (hKB : K ⊆ seedCoordBranch) :
    ∃ S T : _root_.OAI.Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ S ∧ ContDiff ℝ ∞ T ∧
      HasCompactSupport S ∧ HasCompactSupport T ∧
      tsupport S ⊆ seedCoordBranch ∧ tsupport T ⊆ seedCoordBranch ∧
      ∀ x ∈ K, S =ᶠ[𝓝 x] seedCoordReal ∧ T =ᶠ[𝓝 x] seedCoordImag := by
  obtain ⟨S,hS,hSc,hSB,hSe⟩ := compact_smooth_extension hK seedCoordBranch_open hKB
    seedCoordReal seedCoordReal_smoothOn
  obtain ⟨T,hT,hTc,hTB,hTe⟩ := compact_smooth_extension hK seedCoordBranch_open hKB
    seedCoordImag seedCoordImag_smoothOn
  exact ⟨S,T,hS,hT,hSc,hTc,hSB,hTB,fun x hx ↦ ⟨hSe x hx,hTe x hx⟩⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordinateField
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section

lemma seedCoordinateField_smooth (N : ℕ) : ContDiff ℝ ∞ (seedCoordinateField N) :=
  (ambientRealSeed_contDiff N).comp (seedChartAmbient_smooth.comp seedCoordEquiv.contDiff)

lemma seedCoordinateField_log (N : ℕ) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ seedCoordBranch) :
    seedCoordinateField N x = oscillatorySeed seedCoordReal seedCoordImag (N:ℝ) x :=
  ambientSeed_log_trigonometric N hx

lemma seedCoordinateField_log_germ (N : ℕ) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ seedCoordBranch)
    (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : S0 =ᶠ[𝓝 x] seedCoordReal)
    (hT : T0 =ᶠ[𝓝 x] seedCoordImag) :
    seedCoordinateField N =ᶠ[𝓝 x] oscillatorySeed S0 T0 (N:ℝ) := by
  filter_upwards [seedCoordBranch_open.mem_nhds hx,hS,hT] with z hz hs ht
  rw [seedCoordinateField_log N hz]
  simp only [oscillatorySeed,hs,ht]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedCoordPatchTopology
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped Topology
noncomputable section

lemma seedCoordPatch_closure_subset (r : ℝ) :
    closure (seedCoordPatch r) ⊆ seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r :=
  closure_minimal (preimage_mono ball_subset_closedBall)
    (isClosed_closedBall.preimage seedCoordEquiv.continuous)

lemma seedCoordPatch_compactClosure (r : ℝ) : IsCompact (closure (seedCoordPatch r)) := by
  have hc : IsCompact (seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r) := by
    have he : seedCoordEquiv ⁻¹' closedBall (0 : BaseModel) r =
        seedCoordEquiv.symm '' closedBall (0 : BaseModel) r := by
      ext x
      constructor
      · intro hx
        exact ⟨seedCoordEquiv x,hx,seedCoordEquiv.symm_apply_apply x⟩
      · rintro ⟨y,hy,rfl⟩
        simpa using hy
    rw [he]
    exact (isCompact_closedBall _ _).image seedCoordEquiv.symm.continuous
  exact hc.of_isClosed_subset isClosed_closure (seedCoordPatch_closure_subset r)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PlacedSmoothRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma PlacedEnvelopeData.closure_Ω_branch {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    closure d.Ω ⊆ seedCoordBranch :=
  d.closure_Ω_patch.trans (subset_closure.trans (d.patch_V.trans d.V_branch))

theorem PlacedEnvelopeData.smooth_representatives {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    ∃ S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ S ∧ ContDiff ℝ ∞ S0 ∧ ContDiff ℝ ∞ T0 ∧
      ∀ x ∈ closure d.Ω, S =ᶠ[𝓝 x] d.S ∧ S0 =ᶠ[𝓝 x] seedCoordReal ∧
        T0 =ᶠ[𝓝 x] seedCoordImag := by
  obtain ⟨S,hS,_,_,he⟩ := compact_smooth_extension d.compact_closure_Ω
    seedCoordBranch_open d.closure_Ω_branch d.S d.smooth
  obtain ⟨S0,T0,hS0,hT0,_,_,_,_,he0⟩ := seed_log_compact_extensions
    d.compact_closure_Ω d.closure_Ω_branch
  exact ⟨S,S0,T0,hS,hS0,hT0,fun x hx ↦ ⟨he x hx,(he0 x hx).1,(he0 x hx).2⟩⟩

lemma PlacedEnvelopeData.outside_gap {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T)
    (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∉ d.U) : d.S x-seedCoordReal x ≤ -d.gap := by
  have h := d.outer_gap x (fun h ↦ hx (d.C_U h))
  linarith

lemma seeded_sourceFirstJetSize_germ {f f' v : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (h : f =ᶠ[𝓝 x] f') (N : ℝ) :
    sourceFirstJetSize (fun z ↦ f z+v z) N x =
      sourceFirstJetSize (fun z ↦ f' z+v z) N x := by
  have he : (fun z ↦ f z+v z) =ᶠ[𝓝 x] (fun z ↦ f' z+v z) :=
    h.mono (fun z hz ↦ congrArg (· + v z) hz)
  simp only [sourceFirstJetSize,he.eq_of_nhds,he.fderiv_eq]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_PlacedFirstJetProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {r a : ℝ}
  {Kset : Set _root_.OAI.Yau.Jets.Coord}
  {T : ℝ}
  {m J K k0 : ℕ}

lemma PlacedEnvelopeData.literal_good_event_eq (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    (he : ∀ x ∈ closure d.Ω, S =ᶠ[𝓝 x] d.S ∧ S0 =ᶠ[𝓝 x] seedCoordReal ∧
      T0 =ᶠ[𝓝 x] seedCoordImag)
    (n : ℕ) (hfin : Fintype (SourceGrid d.U n)) :
    (d.representativeWaves b S (fun x hx ↦ (he x hx).1)).latticeGoodEvent
      subset_closure n hfin S0 T0 (closure d.Ω) =
    letI := hfin
    coefficientJetGoodEvent
      (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2)
      (seedCoordinateField n) n (closure d.Ω)
      (fun x ↦ ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
        (Real.exp ((n:ℝ)*seedCoordReal x))) := by
  let := hfin
  ext coeff
  simp only [LocalCompactWaveData.latticeGoodEvent,coefficientJetGoodEvent,
    mem_inter_iff,firstJetGoodEvent,mem_ofPred_eq]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  have hg := seedCoordinateField_log_germ n (d.closure_Ω_branch hx) S0 T0
    (he x hx).2.1 (he x hx).2.2
  have hj := seeded_sourceFirstJetSize_germ (v := gaussianWaveField
    (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff) hg (n:ℝ)
  change (_ ≤ sourceFirstJetSize _ _ _) ↔ (_ ≤ sourceFirstJetSize _ _ _)
  rw [hj,(he x hx).1.eq_of_nhds,(he x hx).2.1.eq_of_nhds]
  rfl

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_PlacedNodalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {r a : ℝ}
  {Kset : Set _root_.OAI.Yau.Jets.Coord}
  {T : ℝ}
  {m J K k0 : ℕ}

lemma sourceSignScale_germ {S S' : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (he : S =ᶠ[𝓝 x] S') : sourceSignScale g S x = sourceSignScale g S' x := by
  simp only [sourceSignScale,metricGradient,he.fderiv_eq]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FixedDomainLatticeSuccessfulPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_successful_packing_fixed_domain
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ r : ℝ, 0 < r ∧
      r < tau/4 ∧ r < (1-tau)/2 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (w S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q Ω : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → 5 ≤ k0 →
        ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
        IsCompact Ω → (∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0) →
        ∀ d > 0, (∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) →
        0 < (∫ x in Q, sourceSignScale g S x) →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∃ t : Finset _root_.OAI.Yau.Jets.Coord, ∃ j : t → Fin 4,
          ∃ coeff ∈ a.latticeGoodEvent hUD n hfin S0 T0 Ω, ∃ u : Finset t,
            let R := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
            let f := fun y ↦ oscillatorySeed S0 T0 n y + gaussianWaveField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff y
            (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ Q ∧
            (↑t : Set _root_.OAI.Yau.Jets.Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (R x)) ∧
            (∀ x ∈ t, 0 < R x ∧ sourceClosedBall x (5*R x) ⊆ U) ∧
            (∀ x ∈ u,
              (∀ y ∈ sourceClosedBall x (r*R x), 0 < f y) ∧
              (∀ y ∈ sourceClosedBall ((x : _root_.OAI.Yau.Jets.Coord)+R x • (tau • Pi.single (j x) 1)) (r*R x), f y < 0)) ∧
            c*((n:ℝ)*(∫ x in Q, sourceSignScale g S x)) ≤ ∑ x ∈ u, (R x)^3 := by
  classical
  obtain ⟨tau,ht,ht4,r,hr,hrt,hr1,p,hp0,hprob⟩ := lattice_physical_sign_subballs_fixed_domain g hH hg hp
  let C : ℝ := 2*(Real.pi^2/2)*5^4
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨tau,ht,ht4,r,hr,hrt,hr1,p/(2*C),by positivity,?_⟩
  intro w S S0 T0 D U Q Ω m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hS0 hT0 hk0
    gamma hgamma hgap hΩ hq d hd hout hmass
  filter_upwards [hprob w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
    hS hS0 hT0 hk0 gamma hgamma hgap,
    a.source_sign_scale_packing hQ hU hQU hUD,
    a.lattice_good_event_probability hUD hU hUb hS S0 T0 hS0 hT0 hΩ (by omega) hq hd hout
      (p/4) (by positivity)] with n hsign hpack hgood
  obtain ⟨hfin,hsign⟩ := hsign
  obtain ⟨hfin',hgood⟩ := hgood
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  let : IsProbabilityMeasure (gaussianPairs (ι := SourceGrid U n × Fin 3)) := by
    unfold gaussianPairs; infer_instance
  obtain ⟨hn,t,htQ,htdis,htcov,htU,hvol⟩ := hpack
  let R := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
  let f := fun coeff y ↦ oscillatorySeed S0 T0 n y + gaussianWaveField
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff y
  choose j hj using (fun x : t ↦ hsign x (htQ x.property))
  let A := fun x : t ↦ {coeff |
    (∀ y ∈ sourceClosedBall x (r*R x), 0 < f coeff y) ∧
    (∀ y ∈ sourceClosedBall ((x : _root_.OAI.Yau.Jets.Coord)+R x • (tau • Pi.single (j x) 1)) (r*R x), f coeff y < 0)}
  have hA (x : t) : MeasurableSet (A x) ∧ p ≤ gaussianPairs.real (A x) := by
    simpa only [A,f,R,sourceClosedBall,mem_ofPred_eq,div_eq_mul_inv] using (hj x).2
  have hsum : (∑ x : t, (R x)^3) = ∑ x ∈ t, (R x)^3 := by
    exact Finset.sum_coe_sort t (fun x ↦ (R x)^3)
  have hvol' : (n:ℝ)*(∫ x in Q, sourceSignScale g S x) ≤ C * ∑ x : t, (R x)^3 := by
    rw [hsum]
    exact hvol
  have hT : 0 < ∑ x : t, (R x)^3 := by
    have hh : 0 < (n:ℝ)*(∫ x in Q, sourceSignScale g S x) := mul_pos (by exact_mod_cast hn) hmass
    nlinarith
  have hfail : (gaussianPairs (a.latticeGoodEvent hUD n hfin S0 T0 Ω)ᶜ).toReal < p/2 := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgood.2
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ p/4)] at hh
    linarith
  obtain ⟨coeff,hcoeff,u,hu,hw⟩ := exists_good_successful_tests
    (fun x : t ↦ (R x)^3) (fun x ↦ (pow_pos (htU x x.property).1 3).le) hT
    A (fun x ↦ (hA x).1) hp0 (fun x ↦ (hA x).2)
    (a.latticeGoodEvent hUD n hfin S0 T0 Ω) hgood.1 hfail
  refine ⟨hfin,t,j,coeff,hcoeff,u,htQ,htdis,htU,hu,?_⟩
  calc
    p/(2*C)*((n:ℝ)*(∫ x in Q, sourceSignScale g S x)) ≤
        p/(2*C)*(C*∑ x : t, (R x)^3) := mul_le_mul_of_nonneg_left hvol' (by positivity)
    _ = p*(∑ x : t, (R x)^3)/2 := by field_simp
    _ ≤ _ := hw

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FixedDomainLiteralPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem fixed_domain_literal_successful_packing
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ rf : ℝ, 0 < rf ∧
      rf < tau/4 ∧ rf < (1-tau)/2 ∧ ∃ c > 0, ∀ {w : _root_.OAI.Yau.Jets.Coord → ℝ} {r a : ℝ} {Kset : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} {m J K k0 : ℕ}
    (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (_ : closure d.U ⊆ H)
    (_ : 5 ≤ k0) (_ : ∀ x ∈ closure d.Ω, fderiv ℝ seedCoordImag x ≠ 0)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (_ : IsCompact Q) (_ : Q ⊆ d.U)
    {gamma : ℝ} (_ : 0 < gamma)
    (_ : ∀ x ∈ Q, seedCoordReal x+gamma ≤ d.S x) (_ : 0 < ∫ x in Q, sourceSignScale g d.S x),
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n), letI := hfin
      ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
        let f := fun y ↦ seedCoordinateField n y + gaussianWaveField
          (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff y
        coeff ∈ coefficientEvent (n:ℝ) ∧ ContDiff ℝ ∞ f ∧
        (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
          (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize f n x) ∧
        ∃ t : Finset _root_.OAI.Yau.Jets.Coord, ∃ j : t → Fin 4, ∃ u : Finset t,
          let R := fun x ↦ ((n:ℝ)*sourceSignScale g d.S x)⁻¹
          (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ Q ∧
          (↑t : Set _root_.OAI.Yau.Jets.Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (R x)) ∧
          (∀ x ∈ t, 0 < R x ∧ sourceClosedBall x (5*R x) ⊆ d.U) ∧
          (∀ x ∈ u,
            (∀ y ∈ sourceClosedBall x (rf*R x), 0 < f y) ∧
            (∀ y ∈ sourceClosedBall ((x : _root_.OAI.Yau.Jets.Coord)+R x • (tau • Pi.single (j x) 1))
              (rf*R x), f y < 0)) ∧
          c*((n:ℝ)*(∫ x in Q, sourceSignScale g d.S x)) ≤ ∑ x ∈ u, (R x)^3 := by
  classical
  obtain ⟨tau,ht,ht4,rf,hr,hrt,hr1,c,hc,hcert⟩ := lattice_successful_packing_fixed_domain g hH hg hp
  refine ⟨tau,ht,ht4,rf,hr,hrt,hr1,c,hc,?_⟩
  intro w r a Kset T m J K k0 d b hDH hk0 hq Q hQ hQU gamma hgamma hgap hmass

  obtain ⟨S,S0,T0,hS,hS0,hT0,he⟩ := d.smooth_representatives
  let b' := d.representativeWaves b S (fun x hx ↦ (he x hx).1)
  have hUΩ : d.U ⊆ closure d.Ω := subset_closure.trans (d.closure_U_Ω.trans subset_closure)
  have hq' : ∀ x ∈ closure d.Ω, fderiv ℝ T0 x ≠ 0 := by
    intro x hx
    rw [(he x hx).2.2.fderiv_eq]
    exact hq x hx
  have hout : ∀ x ∈ closure d.Ω, x ∉ d.U → S x-S0 x ≤ -d.gap := by
    intro x hx hxu
    rw [(he x hx).1.eq_of_nhds,(he x hx).2.1.eq_of_nhds]
    exact d.outside_gap x hxu
  have hin : ∀ x ∈ Q, S0 x+gamma ≤ S x := by
    intro x hx
    rw [(he x (hUΩ (hQU hx))).1.eq_of_nhds,(he x (hUΩ (hQU hx))).2.1.eq_of_nhds]
    exact hgap x hx
  have hint : (∫ x in Q, sourceSignScale g S x) = ∫ x in Q, sourceSignScale g d.S x := by
    apply setIntegral_congr_fun hQ.measurableSet
    intro x hx
    exact sourceSignScale_germ (he x (hUΩ (hQU hx))).1
  filter_upwards [hcert w S S0 T0 (closure d.U) d.U Q (closure d.Ω) m J K k0 b'
    d.compact_closure_U hDH subset_closure (subset_closure.trans hDH) d.open_U
    (d.compact_closure_U.isBounded.subset subset_closure) hQ hQU hS hS0 hT0 hk0
    gamma hgamma hin d.compact_closure_Ω hq' d.gap d.gap_pos hout (by rwa [hint]),b.estimates] with n hn hb
  obtain ⟨hfin,t,j,coeff,hcoeff,u,htQ,htdis,htU,hsign,hweight⟩ := hn
  let := hfin
  let V := fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2
  let f := fun y ↦ seedCoordinateField n y+gaussianWaveField V coeff y
  have hf : ContDiff ℝ ∞ f := (seedCoordinateField_smooth n).add
    (gaussianWaveField_contDiff V coeff (fun i ↦ (hb (latticeFrame b.cover subset_closure n i.1,i.2)).1))
  rw [d.literal_good_event_eq b S S0 T0 he n hfin] at hcoeff
  have hRad : ∀ x ∈ t, ((n:ℝ)*sourceSignScale g S x)⁻¹ =
      ((n:ℝ)*sourceSignScale g d.S x)⁻¹ := by
    intro x hx
    rw [sourceSignScale_germ (he x (hUΩ (hQU (htQ hx)))).1]
  have hfield : ∀ y ∈ d.U, f y = oscillatorySeed S0 T0 n y+gaussianWaveField V coeff y := by
    intro y hy
    dsimp [f]
    rw [(seedCoordinateField_log_germ n (d.closure_Ω_branch (hUΩ hy)) S0 T0
      (he y (hUΩ hy)).2.1 (he y (hUΩ hy)).2.2).eq_of_nhds]
  have hsmall (x : t) :
      sourceClosedBall (x:_root_.OAI.Yau.Jets.Coord) (rf*((n:ℝ)*sourceSignScale g d.S x)⁻¹) ⊆ d.U ∧
      sourceClosedBall ((x:_root_.OAI.Yau.Jets.Coord)+((n:ℝ)*sourceSignScale g d.S x)⁻¹ •
        (tau • Pi.single (j x) 1)) (rf*((n:ℝ)*sourceSignScale g d.S x)⁻¹) ⊆ d.U := by
    have hRU := htU x x.property
    dsimp only at hRU
    rw [hRad x x.property] at hRU
    constructor
    · intro y hy
      apply hRU.2
      change sourceEuclideanNorm (y-(x:_root_.OAI.Yau.Jets.Coord)) ≤ _
      exact hy.trans (mul_le_mul_of_nonneg_right (by linarith : rf ≤ 5) hRU.1.le)
    · intro y hy
      apply hRU.2
      change sourceEuclideanNorm (y-(x:_root_.OAI.Yau.Jets.Coord)) ≤ _
      have hh := sourceEuclideanNorm_add_le
        (y-((x:_root_.OAI.Yau.Jets.Coord)+((n:ℝ)*sourceSignScale g d.S x)⁻¹ • (tau • Pi.single (j x) 1)))
        (((n:ℝ)*sourceSignScale g d.S x)⁻¹ • (tau • Pi.single (j x) 1))
      have hadd : y-((x:_root_.OAI.Yau.Jets.Coord)+((n:ℝ)*sourceSignScale g d.S x)⁻¹ • (tau • Pi.single (j x) 1))+
          ((n:ℝ)*sourceSignScale g d.S x)⁻¹ • (tau • Pi.single (j x) 1) = y-(x:_root_.OAI.Yau.Jets.Coord) := by abel
      rw [hadd,sourceEuclideanNorm_smul,abs_of_pos hRU.1,
        sourceEuclideanNorm_single,abs_of_pos ht] at hh
      change sourceEuclideanNorm (y-((x:_root_.OAI.Yau.Jets.Coord)+_)) ≤ _ at hy
      nlinarith
  refine ⟨hfin,coeff,hcoeff.1,hf,hcoeff.2,t,j,u,htQ,?_,?_,?_,?_⟩
  · intro x hx y hy hxy
    simpa only [Function.onFun,hRad x hx,hRad y hy] using htdis hx hy hxy
  · intro x hx
    simpa only [hRad x hx] using htU x hx
  · intro x hx
    have hh := hsign x hx
    change (∀ y ∈ sourceClosedBall (x:_root_.OAI.Yau.Jets.Coord) (rf*((n:ℝ)*sourceSignScale g S x)⁻¹),
      0 < oscillatorySeed S0 T0 n y+gaussianWaveField V coeff y) ∧
      (∀ y ∈ sourceClosedBall ((x:_root_.OAI.Yau.Jets.Coord)+((n:ℝ)*sourceSignScale g S x)⁻¹ •
        (tau • Pi.single (j x) 1)) (rf*((n:ℝ)*sourceSignScale g S x)⁻¹),
        oscillatorySeed S0 T0 n y+gaussianWaveField V coeff y < 0) at hh
    rw [hRad x x.property] at hh
    constructor
    · intro y hy
      change 0 < f y
      rw [hfield y ((hsmall x).1 hy)]
      exact hh.1 y hy
    · intro y hy
      change f y < 0
      rw [hfield y ((hsmall x).2 hy)]
      exact hh.2 y hy
  · change c*((n:ℝ)*(∫ x in Q, sourceSignScale g S x)) ≤
      ∑ x ∈ u, (((n:ℝ)*sourceSignScale g S x)⁻¹)^3 at hweight
    rw [hint] at hweight
    simpa only [hRad _ (Subtype.property _)] using hweight

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicSeedRegularity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

lemma intrinsicSeedCoordMetric_regular (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ContDiff ℝ ∞ (intrinsicSeedCoordMetric A rho) ∧
    (∀ x u v, intrinsicSeedCoordMetric A rho x u v = intrinsicSeedCoordMetric A rho x v u) ∧
    (∀ x v, v ≠ 0 → 0 < intrinsicSeedCoordMetric A rho x v v) := by
  rw [← intrinsicSeedCoordMetric_eq A hs hp rho hrp]
  let c := intrinsicChartCoefficient A rho seedPoint
  have hc : ContDiff ℝ ∞ c := contDiff_iff_contDiffAt.mpr (fun z ↦
    intrinsicChartCoefficient_smoothAt A hA hs hp rho hr seedPoint
      (by rw [centeredSphereChart_target]; trivial))
  have hcp : ∀ z (α : BaseModel →L[ℝ] ℝ), α ≠ 0 → 0 < α ((c z).1 α) :=
    fun z ↦ intrinsicChartCoefficient_positive A hs hp rho seedPoint
      (by rw [centeredSphereChart_target]; trivial)
  exact ⟨seedCoordMetric_smooth c hc hcp,
    seedCoordMetric_symmetric c hcp (fun z ↦ intrinsicChartCoefficient_symmetric A hs rho seedPoint z),
    seedCoordMetric_positive c hcp (fun _ ↦ hrp _)⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedPatchTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff Topology
noncomputable section

lemma seedSpherePatch_closure_subset (r : ℝ) :
    closure (seedSpherePatch r) ⊆
      (extChartAt (𝓡 4) seedPoint).symm '' closedBall (0 : BaseModel) r := by
  apply closure_minimal (image_mono ball_subset_closedBall)
  exact ((isCompact_closedBall _ _).image seedSphereChart_inverse_continuous).isClosed

lemma seedSpherePatch_closure_in_chart (r : ℝ) :
    closure (seedSpherePatch r) ⊆ (extChartAt (𝓡 4) seedPoint).source := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := seedSpherePatch_closure_subset r hx
  exact (extChartAt (𝓡 4) seedPoint).map_target (by rw [centeredSphereChart_target]; trivial)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedDeviationCoordinates
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Yau.Geometry Yau.Jets
open scoped Topology
noncomputable section

lemma seedDeviationCoordinates_eq_image {K : Set Base}
    (hK : K ⊆ (extChartAt (𝓡 4) seedPoint).source) :
    seedDeviationCoordinates K =
      (fun p ↦ seedCoordEquiv.symm (extChartAt (𝓡 4) seedPoint p)) '' K := by
  ext x
  constructor
  · intro hx
    refine ⟨(extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x),hx,?_⟩
    dsimp only
    rw [(extChartAt (𝓡 4) seedPoint).right_inv
      (by rw [centeredSphereChart_target]; trivial),seedCoordEquiv.symm_apply_apply]
  · rintro ⟨p,hp,rfl⟩
    change (extChartAt (𝓡 4) seedPoint).symm
      (seedCoordEquiv (seedCoordEquiv.symm (extChartAt (𝓡 4) seedPoint p))) ∈ K
    rw [seedCoordEquiv.apply_symm_apply,(extChartAt (𝓡 4) seedPoint).left_inv (hK hp)]
    exact hp

lemma seedDeviationCoordinates_compact {K : Set Base} (hK : IsCompact K)
    (hchart : K ⊆ (extChartAt (𝓡 4) seedPoint).source) :
    IsCompact (seedDeviationCoordinates K) := by
  rw [seedDeviationCoordinates_eq_image hchart]
  exact hK.image_of_continuousOn (seedCoordEquiv.symm.continuous.comp_continuousOn
    ((continuousOn_extChartAt seedPoint).mono hchart))

lemma seedDeviationCoordinates_subset_patch {K : Set Base} {r : ℝ}
    (hK : K ⊆ seedSpherePatch r) : seedDeviationCoordinates K ⊆ seedCoordPatch r := by
  intro x hx
  obtain ⟨y,hy,he⟩ := hK hx
  have ht : seedCoordEquiv x ∈ (extChartAt (𝓡 4) seedPoint).target := by
    rw [centeredSphereChart_target]; trivial
  have hy' : y ∈ (extChartAt (𝓡 4) seedPoint).target := by
    rw [centeredSphereChart_target]; trivial
  have heq : y = seedCoordEquiv x :=
    (extChartAt (𝓡 4) seedPoint).symm.injOn hy' ht he
  simpa only [seedCoordPatch,mem_preimage,← heq] using hy

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_FiniteSignPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

lemma compact_positive_margin {E : Type*} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) (f : E → ℝ) (hf : ContinuousOn f K) (hp : ∀ x ∈ K, 0 < f x) :
    ∃ ε > 0, ∀ x ∈ K, ε ≤ f x := by
  rcases K.eq_empty_or_nonempty with h | h
  · refine ⟨1,by norm_num,?_⟩
    simp [h]
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn h hf
    exact ⟨f x,hp x hx,fun y hy ↦ hmin hy⟩

lemma finite_sign_uniform_persistence {ι : Type*} (t : Finset ι)
    (P N : ι → Set _root_.OAI.Yau.Jets.Coord) (hP : ∀ i ∈ t, IsCompact (P i)) (hN : ∀ i ∈ t, IsCompact (N i))
    (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : Continuous f)
    (hsign : ∀ i ∈ t, (∀ x ∈ P i, 0 < f x) ∧ (∀ x ∈ N i, f x < 0)) :
    ∃ ε > 0, ∀ g : _root_.OAI.Yau.Jets.Coord → ℝ,
      (∀ i ∈ t, ∀ x ∈ P i ∪ N i, |g x-f x| < ε) →
      ∀ i ∈ t, (∀ x ∈ P i, 0 < g x) ∧ (∀ x ∈ N i, g x < 0) := by
  have hp : ∀ x ∈ ⋃ i ∈ t, P i, 0 < f x := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    exact (hsign i hi).1 x hx
  have hn : ∀ x ∈ ⋃ i ∈ t, N i, 0 < -f x := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    exact neg_pos.mpr ((hsign i hi).2 x hx)
  obtain ⟨εp,hεp,hpm⟩ := compact_positive_margin (t.isCompact_biUnion hP) f hf.continuousOn hp
  obtain ⟨εn,hεn,hnm⟩ := compact_positive_margin (t.isCompact_biUnion hN) (fun x ↦ -f x) hf.neg.continuousOn hn
  refine ⟨min εp εn,lt_min hεp hεn,?_⟩
  intro g hg i hi
  constructor
  · intro x hx
    have hm := hpm x (mem_iUnion₂.mpr ⟨i,hi,hx⟩)
    have he := abs_lt.mp (hg i hi x (Or.inl hx))
    have hh := min_le_left εp εn
    linarith
  · intro x hx
    have hm := hnm x (mem_iUnion₂.mpr ⟨i,hi,hx⟩)
    have he := abs_lt.mp (hg i hi x (Or.inr hx))
    have hh := min_le_right εp εn
    linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_LiteralNodalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

theorem literal_nodal_certificate_of_packing
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (Q U : Set _root_.OAI.Yau.Jets.Coord) (n : ℕ) (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : Continuous f)
    (tau rf : ℝ) (ht : 0 < tau) (ht4 : tau < 1/4) (hr : 0 < rf)
    (hrt : rf < tau/4) (hr1 : rf < (1-tau)/2)
    (t : Finset _root_.OAI.Yau.Jets.Coord) (j : t → Fin 4) (u : Finset t) (M : ℝ)
    (htQ : (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ Q)
    (hdis : (↑t : Set _root_.OAI.Yau.Jets.Coord).PairwiseDisjoint
      (fun x ↦ sourceClosedBall x (((n:ℝ)*sourceSignScale g S x)⁻¹)))
    (hU : ∀ x ∈ t, 0 < ((n:ℝ)*sourceSignScale g S x)⁻¹ ∧
      sourceClosedBall x (5*((n:ℝ)*sourceSignScale g S x)⁻¹) ⊆ U)
    (hsign : ∀ x ∈ u,
      (∀ y ∈ sourceClosedBall x (rf*((n:ℝ)*sourceSignScale g S x)⁻¹), 0 < f y) ∧
      (∀ y ∈ sourceClosedBall ((x:_root_.OAI.Yau.Jets.Coord)+((n:ℝ)*sourceSignScale g S x)⁻¹ •
        (tau • Pi.single (j x) 1)) (rf*((n:ℝ)*sourceSignScale g S x)⁻¹), f y < 0))
    (hweight : M ≤ 2*rf^3*∑ x ∈ u, (((n:ℝ)*sourceSignScale g S x)⁻¹)^3) :
    LiteralNodalCertificate g S Q U n f M := by
  let R := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
  let P := fun x : t ↦ sourceClosedBall (x:_root_.OAI.Yau.Jets.Coord) (rf*R x)
  let N := fun x : t ↦ sourceClosedBall ((x:_root_.OAI.Yau.Jets.Coord)+R x • (tau • Pi.single (j x) 1)) (rf*R x)
  have hp : ∀ y ∈ ⋃ x ∈ u, P x, 0 < f y := by
    intro y hy
    obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
    exact (hsign x hx).1 y hy
  have hn : ∀ y ∈ ⋃ x ∈ u, N x, 0 < -f y := by
    intro y hy
    obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
    exact neg_pos.mpr ((hsign x hx).2 y hy)
  obtain ⟨ep,hep,hpm⟩ := compact_positive_margin
    (u.isCompact_biUnion (fun x _ ↦ sourceClosedBall_isCompact _ _)) f hf.continuousOn hp
  obtain ⟨en,hen,hnm⟩ := compact_positive_margin
    (u.isCompact_biUnion (fun x _ ↦ sourceClosedBall_isCompact _ _))
    (fun y ↦ -f y) hf.neg.continuousOn hn
  obtain ⟨es,hes,hpersist⟩ := finite_sign_uniform_persistence u P N
    (fun x _ ↦ sourceClosedBall_isCompact _ _) (fun x _ ↦ sourceClosedBall_isCompact _ _) f hf hsign
  let mu := min ep (min en es)
  have hmu : 0 < mu := lt_min hep (lt_min hen hes)
  refine ⟨tau,rf,ht,ht4,hr,hrt,hr1,t,j,u,htQ,hdis,hU,hweight,mu,hmu,?_,?_⟩
  · intro x hx
    constructor
    · intro y hy
      exact (min_le_left _ _).trans (hpm y (mem_iUnion₂.mpr ⟨x,hx,hy⟩))
    · intro y hy
      have hm := hnm y (mem_iUnion₂.mpr ⟨x,hx,hy⟩)
      have hh : mu ≤ en := (min_le_right _ _).trans (min_le_left _ _)
      linarith
  · intro v hv hclose
    have hsign' := hpersist v (fun x hx y hy ↦
      (hclose x hx y hy).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    have hdis' : (↑u : Set t).PairwiseDisjoint (fun x ↦ sourceClosedBall (x:_root_.OAI.Yau.Jets.Coord) (R x)) := by
      intro x _ y _ hxy
      exact hdis x.property y.property (fun h ↦ hxy (Subtype.ext h))
    have hU' : ∀ x ∈ u, sourceClosedBall (x:_root_.OAI.Yau.Jets.Coord) (R x) ⊆ U := by
      intro x hx y hy
      apply (hU x x.property).2
      change sourceEuclideanNorm (y-(x:_root_.OAI.Yau.Jets.Coord)) ≤ 5*R x
      exact hy.trans (by linarith [(hU x x.property).1])
    exact (ENNReal.ofReal_le_ofReal hweight).trans
      (finite_nodal_cylinder_measure u v hv (fun x : t ↦ (x:_root_.OAI.Yau.Jets.Coord)) (fun x : t ↦ R x) j
        ht.le hr.le (by linarith) (fun x _ ↦ (hU x x.property).1) hdis' hU' hsign')

theorem LiteralNodalCertificate.measure
    {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {S : _root_.OAI.Yau.Jets.Coord → ℝ}
    {Q U : Set _root_.OAI.Yau.Jets.Coord} {n : ℕ} {f : _root_.OAI.Yau.Jets.Coord → ℝ} {M : ℝ}
    (h : LiteralNodalCertificate g S Q U n f M) (hf : Continuous f) :
    ENNReal.ofReal M ≤ Measure.hausdorffMeasure (4:ℝ)
      ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | f y.1 = 0}) := by
  obtain ⟨tau,rf,ht,ht4,hr,hrt,hr1,t,j,u,htQ,hdis,hU,hw,mu,hmu,hs,hp⟩ := h
  exact hp f hf (by intro x hx y hy; simpa using hmu)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_FixedDomainPackedNodal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem fixed_domain_literal_nodal_certificate_with_packing
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ c > 0, ∀ {w : _root_.OAI.Yau.Jets.Coord → ℝ} {r a : ℝ} {Kset : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} {m J K k0 : ℕ}
    (d : PlacedEnvelopeData g r a Kset T)
    (b : LocalCompactWaveData g w d.S (closure d.U) m J K k0)
    (_ : closure d.U ⊆ H)
    (_ : 5 ≤ k0) (_ : ∀ x ∈ closure d.Ω, fderiv ℝ seedCoordImag x ≠ 0)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (_ : IsCompact Q) (_ : Q ⊆ d.U)
    {gamma : ℝ} (_ : 0 < gamma)
    (_ : ∀ x ∈ Q, seedCoordReal x+gamma ≤ d.S x) (_ : volume Q ≠ 0),
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n), letI := hfin
      ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
        let f := fun y ↦ seedCoordinateField n y + gaussianWaveField
          (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff y
        coeff ∈ coefficientEvent (n:ℝ) ∧ ContDiff ℝ ∞ f ∧
        (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
          (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize f n x) ∧
        ENNReal.ofReal (c*((n:ℝ)*(∫ x in Q, sourceSignScale g d.S x))) ≤
          Measure.hausdorffMeasure (4:ℝ)
            ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | f y.1 = 0}) ∧
        LiteralNodalCertificate g d.S Q d.U n f
          (c*((n:ℝ)*(∫ x in Q, sourceSignScale g d.S x))) := by
  classical
  obtain ⟨tau,ht,ht4,rf,hr,hrt,hr1,c,hc,hpack⟩ :=
    fixed_domain_literal_successful_packing g hH hg hp
  refine ⟨2*rf^3*c,by positivity,?_⟩
  intro w r a Kset T m J K k0 d b hDH hk0 hq Q hQ hQU gamma hgamma hgap hvolume
  have hmass := b.source_sign_mass_pos hQ hvolume (hQU.trans subset_closure)
  filter_upwards [hpack d b hDH hk0 hq hQ hQU hgamma hgap hmass] with n hn
  obtain ⟨hfin,coeff,hcoeff,hf,hjet,t,j,u,htQ,htdis,htU,hsign,hweight⟩ := hn
  let := hfin
  let f := fun y ↦ seedCoordinateField n y+gaussianWaveField
    (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff y
  have hweight' : (2*rf^3*c)*((n:ℝ)*(∫ x in Q, sourceSignScale g d.S x)) ≤
      2*rf^3*∑ x ∈ u, (((n:ℝ)*sourceSignScale g d.S x)⁻¹)^3 := by
    have hh := mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ 2*rf^3)
    simpa only [mul_assoc] using hh
  have hcert := literal_nodal_certificate_of_packing g d.S Q d.U n f hf.continuous
    tau rf ht ht4 hr hrt hr1 t j u _ htQ htdis htU hsign hweight'
  exact ⟨hfin,coeff,hcoeff,hf,hjet,hcert.measure hf.continuous,hcert⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicPackedSelectedStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem intrinsic_packed_selected_stage_oai :
    ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
      seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
      ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
        (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ rho : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho → (∀ x, 0 < rho x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A rho seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A rho seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ K : Set Base, IsCompact K → K ⊆ seedSpherePatch r →
      (∀ x ∉ K, ∀ v w : AmbientBase,
        ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
        A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫) →
      (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∀ (T : ℝ) (k0 K' : ℕ), 5 ≤ k0 →
      ∃ d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T,
    ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set _root_.OAI.Yau.Jets.Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let v := gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
            let u := fun x ↦ seedCoordinateField n x+v x
            let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n)
            coeff ∈ coefficientEvent (n:ℝ) ∧
            ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ (R u) ∧
            R u = (fun x ↦ R (seedCoordinateField n) x+R v x) ∧
            tsupport (R u) ⊆ Q ∧
            (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k (R u) x = 0) ∧
            (∀ x : _root_.OAI.Yau.Jets.Coord,
              DerivativeBound k0 (R u) x
                (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) ∧
            (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
              (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize u n x) ∧
            ENNReal.ofReal (c*((n:ℝ)*(∫ x in seedCoordCube a,
              sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
              Measure.hausdorffMeasure (4:ℝ)
                ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | u y.1 = 0}) ∧
            LiteralNodalCertificate (intrinsicSeedCoordMetric A rho) d.S (seedCoordCube a) d.U n u
              (c*((n:ℝ)*(∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) := by
  obtain ⟨r,a,δ,hr,ha,hδ,hDP,hPB,hq,hplace⟩ := intrinsic_noncritical_placed_data
  refine ⟨r,a,δ,hr,ha,hδ,hDP,hPB,?_⟩
  intro A hAs hs hp rho hrs hrp hclose K hK hKP hA hρ
  have hreg := intrinsicSeedCoordMetric_regular A hAs hs hp rho hrs hrp
  obtain ⟨c,hc,hcertAll⟩ := fixed_domain_literal_nodal_certificate_with_packing
    (intrinsicSeedCoordMetric A rho) (seedCoordPatch_compactClosure r)
    hreg.1.continuous.continuousOn (fun y _ ↦ hreg.2.2 y)
  refine ⟨c,hc,?_⟩
  intro T k0 K' hk0
  have hchart : K ⊆ (extChartAt (𝓡 4) seedPoint).source :=
    hKP.trans (subset_closure.trans (seedSpherePatch_closure_in_chart r))
  obtain ⟨d⟩ := hplace A hAs hs hp rho hrs hrp hclose (seedDeviationCoordinates K)
    (seedDeviationCoordinates_compact hK hchart) (seedDeviationCoordinates_subset_patch hKP) T
  obtain ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,hres⟩ :=
    intrinsic_placed_total_residual A hAs hs hp rho hrs hrp d ha.le hK hchart hA hρ k0 K'
  have hcube : seedCoordCube a ⊆ d.U := fun x hx ↦ d.C_U (d.inner_C (Or.inl hx))
  have hvolume : MeasureTheory.volume (seedCoordCube a) ≠ 0 := by
    simp only [seedCoordCube,Real.volume_Icc_pi,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    apply pow_ne_zero
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hcert := hcertAll d b
    (d.closure_U_Ω.trans (subset_closure.trans (d.closure_Ω_patch.trans subset_closure))) hk0
    (fun x hx ↦ hq x (subset_closure (d.closure_Ω_patch hx)))
    (show IsCompact (seedCoordCube a) from isCompact_Icc) hcube d.gap_pos
    (fun x hx ↦ d.inner_gap x (Or.inl hx)) hvolume
  refine ⟨d,b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hres,hcert] with n hn hc
  obtain ⟨hfin,hn⟩ := hn
  obtain ⟨hfin',coeff,hcoeff,hf,hjet,hmeasure,hpacking⟩ := hc
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  have hr := hn coeff
  exact ⟨hfin,coeff,hcoeff,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,
    hr.2.2.2.2.1,hr.2.2.2.2.2 hcoeff,hjet,hmeasure,hpacking⟩

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.intrinsic_packed_selected_stage_oai := @OAI.Yau.Target.intrinsic_packed_selected_stage_oai
