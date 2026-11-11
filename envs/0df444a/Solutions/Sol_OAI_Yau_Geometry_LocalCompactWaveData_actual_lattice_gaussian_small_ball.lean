-- Prove2me | solution 1 for OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:27:43.972208+00:00
-- url     : https://prove2.me/submissions/bdfe7b39-be38-4e37-83b5-5d987afa686f

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Floor.Ring
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
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
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
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
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
import Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_lattice_logarithmic_jet_estimates

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
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AdmissibleChartPatch
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
attribute [local instance] clmTopology clmAdd clmModule

lemma sourceHessian_continuous (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (sourceHessian g S) := by
  have hD := hS.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact ((hS.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).sub
    (((ContinuousLinearMap.compL ℝ _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord ℝ).continuous.comp hD).clm_comp
      (smooth_metric_connection_continuous g hg hp))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransverseSpanning
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

lemma perpendicular_span_le_ker (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (p : _root_.OAI.Yau.Jets.Coord) (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (hperp : ∀ j, g p (q j) = 0) :
    Submodule.span ℝ (range q) ≤ (g p).toLinearMap.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact hperp j

lemma perpendicular_triple_basis (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (p : _root_.OAI.Yau.Jets.Coord) (hp0 : p ≠ 0)
    (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : LinearIndependent ℝ q) (hperp : ∀ j, g p (q j) = 0) :
    Submodule.span ℝ (range (Fin.cons p q)) = ⊤ := by
  have hnot : p ∉ Submodule.span ℝ (range q) := by
    intro h
    have hh := perpendicular_span_le_ker g p q hperp h
    exact (ne_of_gt (hp p hp0)) hh
  have hi : LinearIndependent ℝ (Fin.cons p q) := linearIndependent_finCons.mpr ⟨hq,hnot⟩
  exact hi.span_eq_top_of_card_eq_finrank' (by simp [_root_.OAI.Yau.Jets.Coord])

theorem perpendicular_triple_spans (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (p : _root_.OAI.Yau.Jets.Coord) (hp0 : p ≠ 0)
    (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : LinearIndependent ℝ q) (hperp : ∀ j, g p (q j) = 0)
    (v : _root_.OAI.Yau.Jets.Coord) (hv : g p v = 0) : v ∈ Submodule.span ℝ (range q) := by
  have htop := perpendicular_triple_basis g hp p hp0 q hq hperp
  have hvtop : v ∈ Submodule.span ℝ (insert p (range q)) := by
    rw [← Fin.range_cons,htop]
    trivial
  obtain ⟨a,u,hu,rfl⟩ := Submodule.mem_span_insert.mp hvtop
  have hgu : g p u = 0 := perpendicular_span_le_ker g p q hperp hu
  have ha : a = 0 := by
    have hh : a * g p p = 0 := by simpa [map_add,map_smul,smul_eq_mul,hgu] using hv
    exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt (hp p hp0))
  simpa [ha] using hu

theorem transverseEnergy_pos (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (p : _root_.OAI.Yau.Jets.Coord) (hp0 : p ≠ 0)
    (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : LinearIndependent ℝ q) (hperp : ∀ j, g p (q j) = 0)
    (v : _root_.OAI.Yau.Jets.Coord) (hv : g p v = 0) (hv0 : v ≠ 0) : 0 < transverseEnergy g q v := by
  have hnon : 0 ≤ transverseEnergy g q v := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  apply lt_of_le_of_ne hnon
  intro hz
  have hzero : ∀ j, g (q j) v = 0 := by
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
      sq_nonneg (g (q j) v))).mp hz.symm
    intro j
    exact (sq_eq_zero_iff).mp (he j (Finset.mem_univ j))
  have hker : Submodule.span ℝ (range q) ≤ (g.flip v).toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hzero j
  have hgv : g v v = 0 := hker (perpendicular_triple_spans g hp p hp0 q hq hperp v hv)
  exact (ne_of_gt (hp v hv0)) hgv

lemma transverseEnergy_smul (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (q : Fin 3 → _root_.OAI.Yau.Jets.Coord) (v : _root_.OAI.Yau.Jets.Coord) (a : ℝ) :
    transverseEnergy g q (a • v) = a^2 * transverseEnergy g q v := by
  simp [transverseEnergy,map_smul,smul_eq_mul,mul_pow,Finset.mul_sum]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformTripleBounds
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

omit [CompactSpace T] in
lemma transverseEnergy_continuous
    (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : Continuous g)
    (q : T → Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : Continuous q) :
    Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ transverseEnergy (g z.1) (q z.1) z.2) := by
  apply continuous_finsetSum
  intro j _
  exact (((hg.comp continuous_fst).clm_apply
    (((continuous_apply j).comp hq).comp continuous_fst)).clm_apply continuous_snd).pow 2

theorem uniform_transverse_spanning
    (g : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : Continuous g)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (q : T → Fin 3 → _root_.OAI.Yau.Jets.Coord) (hq : Continuous q)
    (hqi : ∀ t, LinearIndependent ℝ (q t)) (hperp : ∀ t j, g t (p t) (q t j) = 0) :
    ∃ c > 0, ∀ t v, g t (p t) v = 0 → c*‖v‖^2 ≤ transverseEnergy (g t) (q t) v := by
  let A : Set (T × _root_.OAI.Yau.Jets.Coord) := (univ ×ˢ Metric.sphere 0 1) ∩ {z | g z.1 (p z.1) z.2 = 0}
  have hcompact : IsCompact A :=
    (isCompact_univ.prod (isCompact_sphere (0:_root_.OAI.Yau.Jets.Coord) 1)).inter_right
      (isClosed_eq (((hg.comp continuous_fst).clm_apply (hp.comp continuous_fst)).clm_apply
        continuous_snd) continuous_const)
  have hpositive : ∀ z ∈ A, 0 < transverseEnergy (g z.1) (q z.1) z.2 := by
    intro z hz
    apply transverseEnergy_pos (g z.1) (hpos z.1) (p z.1) (hp0 z.1)
      (q z.1) (hqi z.1) (hperp z.1) z.2 hz.2
    intro he
    have hn := hz.1.2
    simp [he] at hn
  obtain ⟨c,hc,C,hC,hbound⟩ := compact_positive_bounds hcompact _
    (transverseEnergy_continuous g hg q hq).continuousOn hpositive
  refine ⟨c,hc,?_⟩
  intro t v hv
  by_cases hz : v = 0
  · simp [hz,transverseEnergy]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  have hunit : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ (ne_of_gt hn)]
  have hmem : (t,(‖v‖⁻¹ : ℝ) • v) ∈ A := by
    exact ⟨⟨mem_univ t,by simpa only [Metric.mem_sphere,dist_zero_right] using hunit⟩,
      by simp [map_smul,smul_eq_mul,hv]⟩
  have hh := (hbound _ hmem).1
  rw [transverseEnergy_smul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have hn0 : ‖v‖ ≠ 0 := ne_of_gt hn
  have he : ‖v‖^2 * ((‖v‖⁻¹)^2 * transverseEnergy (g t) (q t) v) =
      transverseEnergy (g t) (q t) v := by field_simp
  rw [he] at hmul
  nlinarith

theorem uniform_direction_strictness
    (g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : Continuous g) (hH : Continuous H)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (d : AdmissibleFrameTriple g H p) :
    ∃ c > 0, ∃ C > 0, ∀ t j,
      c ≤ sourceDirectionEta (g t) (H t) (p t) (d.q t j) ∧
      sourceDirectionEta (g t) (H t) (p t) (d.q t j) ≤ C := by
  have hq : Continuous (fun z : T × Fin 3 ↦ d.q z.1 z.2) :=
    continuous_prod_of_discrete_right.mpr (fun j ↦ (continuous_apply j).comp d.continuous_q)
  have hgP : Continuous (fun z : T × Fin 3 ↦ g z.1 (p z.1) (p z.1)) := ((hg.comp continuous_fst).clm_apply (hp.comp continuous_fst)).clm_apply (hp.comp continuous_fst)
  have hgQ : Continuous (fun z : T × Fin 3 ↦ g z.1 (d.q z.1 z.2) (d.q z.1 z.2)) := ((hg.comp continuous_fst).clm_apply hq).clm_apply hq
  have hHP : Continuous (fun z : T × Fin 3 ↦ H z.1 (p z.1) (p z.1)) := ((hH.comp continuous_fst).clm_apply (hp.comp continuous_fst)).clm_apply (hp.comp continuous_fst)
  have hHQ : Continuous (fun z : T × Fin 3 ↦ H z.1 (d.q z.1 z.2) (d.q z.1 z.2)) := ((hH.comp continuous_fst).clm_apply hq).clm_apply hq
  have hden (z : T × Fin 3) : 0 < g z.1 (p z.1) (p z.1)+g z.1 (d.q z.1 z.2) (d.q z.1 z.2) := by
    rw [d.length]
    have hh := hpos z.1 (p z.1) (hp0 z.1)
    linarith
  have heta : Continuous (fun z : T × Fin 3 ↦ sourceDirectionEta (g z.1) (H z.1)
      (p z.1) (d.q z.1 z.2)) := (hHP.add hHQ).div (hgP.add hgQ) (fun z ↦ ne_of_gt (hden z))
  obtain ⟨c,hc,C,hC,hb⟩ := compact_positive_bounds isCompact_univ _ heta.continuousOn
    (fun z _ ↦ div_pos (d.strict z.1 z.2) (hden z))
  exact ⟨c,hc,C,hC,fun t j ↦ hb (t,j) (mem_univ _)⟩

end
end Yau.Geometry

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

lemma bilinear_pairing_bound (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (u v : _root_.OAI.Yau.Jets.Coord) :
    |g u v| ≤ ‖g‖*‖u‖*‖v‖ :=
  ((g u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (g.le_opNorm u) (norm_nonneg v))

lemma rounded_positive_pairing (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (mu B K h : ℝ) (hmu : 0 < mu) (hB : 0 ≤ B) (hK : 0 ≤ K) (hh : 0 ≤ h)
    (hg : ‖g‖ ≤ B) (hc : ∀ v, mu*‖v‖^2 ≤ g v v)
    (hlarge : 2*B+1 ≤ K*mu) (x y v : _root_.OAI.Yau.Jets.Coord)
    (hround : ‖y-(x+(K*h) • ((‖v‖⁻¹:ℝ) • v))‖ ≤ 2*h) :
    g (x-y) v ≤ -h*‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  let u := (‖v‖⁻¹:ℝ) • v
  let e := y-(x+(K*h) • u)
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : mu*‖v‖ ≤ g u v := by
    have h := mul_le_mul_of_nonneg_left (hc v) (inv_nonneg.mpr hn.le)
    have he : ‖v‖⁻¹*(mu*‖v‖^2) = mu*‖v‖ := by field_simp
    rw [he] at h
    simpa [u,map_smul,smul_apply,smul_eq_mul] using h
  have he : |g e v| ≤ (2*B*h)*‖v‖ := (bilinear_pairing_bound g e v).trans (by
    have hb : ‖e‖ ≤ 2*h := hround
    calc
      ‖g‖*‖e‖*‖v‖ ≤ B*(2*h)*‖v‖ := by gcongr
      _ = _ := by ring)
  have hid : x-y = -(K*h) • u-e := by dsimp [e]; module
  rw [hid,map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hunit (mul_nonneg hK hh)
  have h2 := mul_le_mul_of_nonneg_right hlarge (mul_nonneg hh (norm_nonneg v))
  have h3 := (abs_le.mp he).1
  nlinarith

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinateNorm
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma sourceEuclideanNorm_le (x : _root_.OAI.Yau.Jets.Coord) : sourceEuclideanNorm x ≤ 2*‖x‖ := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hh (i : Fin 4) : (x i)^2 ≤ ‖x‖^2 := by
    have hi := norm_le_pi_norm x i
    change |x i| ≤ ‖x‖ at hi
    nlinarith [sq_abs (x i),norm_nonneg x,abs_nonneg (x i)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) ↦ hh i)
  norm_num at hs
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_DualWaveCoefficient
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma dualWaveCoefficient_factor (N : ℝ) (V : _root_.OAI.Yau.Jets.Coord → ℂ) (S : ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (b : ℝ) (v : _root_.OAI.Yau.Jets.Coord) (hn : V x ≠ 0) :
    dualWaveCoefficient N V S x b v = (Real.exp (-N*S):ℂ)*V x*((b:ℂ)+normalizedLogJet N V x v) := by
  unfold dualWaveCoefficient normalizedLogJet
  field_simp [hn]

lemma real_log_product_le_coefficient (N : ℝ) (V : _root_.OAI.Yau.Jets.Coord → ℂ) (S : ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (b : ℝ) (v : _root_.OAI.Yau.Jets.Coord) (hn : V x ≠ 0) :
    (‖V x‖*Real.exp (-N*S))*|b+(normalizedLogJet N V x v).re| ≤
      ‖dualWaveCoefficient N V S x b v‖ := by
  rw [dualWaveCoefficient_factor N V S x b v hn,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have h := Complex.abs_re_le_norm ((b:ℂ)+normalizedLogJet N V x v)
  simp only [Complex.add_re,Complex.ofReal_re] at h
  have hh := mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg (V x)) (Real.exp_pos (-N*S)).le)
  simpa only [mul_comm (Real.exp (-N*S)) ‖V x‖] using hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GaussianCoefficientVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma variance_pairLinearSum (z : ι → ℂ) :
    Var[pairLinearSum z; gaussianPairs] = ∑ i, ‖z i‖^2 := by
  classical
  have hf : pairLinearSum z = ∑ p : ι × Fin 2, (fun a : ι × Fin 2 → ℝ ↦
      (if p.2 = 0 then (z p.1).re else -(z p.1).im)*a p) := by
    funext a
    simp [pairLinearSum]
  rw [hf]
  unfold gaussianPairs
  rw [variance_sum_pi]
  · change (∑ p : ι × Fin 2, Var[fun x : ℝ ↦
        (if p.2 = 0 then (z p.1).re else -(z p.1).im) * id x; gaussianReal 0 1]) = _
    simp_rw [variance_const_mul,variance_id_gaussianReal]
    simp only [mul_one,NNReal.coe_one,Fintype.sum_prod_type,Fin.sum_univ_succ,
      Fin.isValue,Fin.succ_ne_zero,ite_true, if_true,ite_false, if_false,Fin.sum_univ_zero,add_zero,neg_sq]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.normSq_apply,pow_two] using (Complex.sq_norm (z i)).symm
  · exact fun p ↦ IsGaussian.memLp_two_id.const_mul _

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PairedJetControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section

lemma paired_products_control (b v Rp Rm h c F : ℝ)
    (hv : 0 ≤ v) (hh : 0 < h) (hh1 : h ≤ 1) (hc : 0 < c) (hF : 0 ≤ F)
    (hd : c*h*v ≤ Rp-Rm) (hb : |b| ≤ |Rp|+F*v) :
    (c^2/(2*(c+F+1)^2))*h^2*(b^2+v^2) ≤ Rp^2+Rm^2 := by
  let q := |Rp|+|Rm|
  have hq : 0 ≤ q := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hdiff : Rp-Rm ≤ q := by dsimp [q] <;> linarith [le_abs_self Rp,neg_le_abs Rm]
  have hcv : c*h*v ≤ q := hd.trans hdiff
  have hcb : c*h*|b| ≤ (c+F)*q := by
    have h1 := mul_le_mul_of_nonneg_left hb (mul_nonneg hc.le hh.le)
    have h2 := mul_le_mul_of_nonneg_left hcv hF
    have h3 : h*|Rp| ≤ q := (mul_le_mul_of_nonneg_right hh1 (abs_nonneg Rp)).trans
      (by dsimp [q] <;> linarith [abs_nonneg Rm])
    have h4 := mul_le_mul_of_nonneg_left h3 hc.le
    nlinarith
  have hs : c*h*(|b|+v) ≤ (c+F+1)*q := by nlinarith
  have hs0 : 0 ≤ c*h*(|b|+v) := by positivity
  have hs2 := pow_le_pow_left₀ hs0 hs 2
  have hb2 : b^2+v^2 ≤ (|b|+v)^2 := by nlinarith [sq_abs b,mul_nonneg (abs_nonneg b) hv]
  have hq2 : q^2 ≤ 2*(Rp^2+Rm^2) := by
    dsimp [q]
    nlinarith [sq_abs Rp,sq_abs Rm,sq_nonneg (|Rp|-|Rm|)]
  have hp : 0 < 2*(c+F+1)^2 := by positivity
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (div_le_iff₀ hp).mpr
  have hleft := mul_le_mul_of_nonneg_left hb2 (by positivity : 0 ≤ c^2*h^2)
  have hright := mul_le_mul_of_nonneg_left hq2 (sq_nonneg (c+F+1))
  nlinarith

lemma opposite_real_products (B Rp Rm ep em pp pm h v a E : ℝ)
    (hh : 0 ≤ h) (hv : 0 ≤ v) (ha : 0 ≤ a)
    (hep : a ≤ ep) (hem : a ≤ em)
    (hpp : pp ≤ -h*v) (hpm : h*v ≤ pm)
    (hRp : |Rp-(B-ep*pp)| ≤ E*h^2*v)
    (hRm : |Rm-(B-em*pm)| ≤ E*h^2*v)
    (hsmall : 2*E*h ≤ a) : a*h*v ≤ Rp-Rm := by
  have hp0 : pp ≤ 0 := hpp.trans (by nlinarith)
  have hm0 : 0 ≤ pm := (mul_nonneg hh hv).trans hpm
  have hpp' : ep*pp ≤ -a*h*v := by
    have h1 := mul_le_mul_of_nonpos_right hep hp0
    have h2 := mul_le_mul_of_nonneg_left hpp ha
    nlinarith
  have hpm' : a*h*v ≤ em*pm := by
    have h1 := mul_le_mul_of_nonneg_right hem hm0
    have h2 := mul_le_mul_of_nonneg_left hpm ha
    nlinarith
  obtain ⟨hpl,hpu⟩ := abs_le.mp hRp
  obtain ⟨hml,hmu⟩ := abs_le.mp hRm
  have he := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hh hv)
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteJetEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section

lemma two_coefficient_energy {ι : Type*} [Fintype ι]
    (f : ι → ℂ) (p m : ι) (s Rp Rm : ℝ) (hs : 0 ≤ s)
    (hp : s*|Rp| ≤ ‖f p‖) (hm : s*|Rm| ≤ ‖f m‖) :
    s^2*(Rp^2+Rm^2) ≤ 2*∑ i, ‖f i‖^2 := by
  classical
  have hpp := pow_le_pow_left₀ (mul_nonneg hs (abs_nonneg Rp)) hp 2
  have hmm := pow_le_pow_left₀ (mul_nonneg hs (abs_nonneg Rm)) hm 2
  rw [mul_pow,sq_abs] at hpp hmm
  have hpS : ‖f p‖^2 ≤ ∑ i, ‖f i‖^2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg ‖f i‖) (Finset.mem_univ p)
  have hmS : ‖f m‖^2 ≤ ∑ i, ‖f i‖^2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg ‖f i‖) (Finset.mem_univ m)
  nlinarith

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

lemma half_scale_square {N : ℝ} (hN : 0 < N) : (N^(-1/2:ℝ))^2 = N⁻¹ := by
  rw [← Real.rpow_mul_natCast hN.le]
  norm_num
  exact Real.rpow_neg_one N

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalDirectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem original_direction_bounds : ∃ cs > 0, ∃ ce > 0, ∃ Ce > 0,
    ∀ t : a.cover.Parameter,
      (∀ v, g (coverSourceCenter a.cover t) (metricGradient g S (coverSourceCenter a.cover t)) v = 0 →
        cs*‖v‖^2 ≤ transverseEnergy (g (coverSourceCenter a.cover t)) (a.cover.triple.q t) v) ∧
      ∀ j, ce ≤ sourceDirectionEta (g (coverSourceCenter a.cover t))
        (sourceHessian g S (coverSourceCenter a.cover t)) (metricGradient g S (coverSourceCenter a.cover t))
        (a.cover.triple.q t j) ∧
        sourceDirectionEta (g (coverSourceCenter a.cover t))
          (sourceHessian g S (coverSourceCenter a.cover t)) (metricGradient g S (coverSourceCenter a.cover t))
          (a.cover.triple.q t j) ≤ Ce := by
  let y := coverSourceCenter a.cover
  have hy := continuous_coverSourceCenter a.cover
  have hp := (metricGradient_continuous a.G a.smooth_G a.positive_G a.A a.smooth_A).comp hy
  have hH := (sourceHessian_continuous a.G a.smooth_G a.positive_G a.A a.smooth_A).comp hy
  have hn (t : a.cover.Parameter) : metricGradient a.G a.A (y t) ≠ 0 :=
    a.nonzero_gradient _ (a.cover.center t).property
  obtain ⟨cs,hcs,hspan⟩ := uniform_transverse_spanning (a.G ∘ y) (a.smooth_G.continuous.comp hy)
    (fun t ↦ a.positive_G _) (metricGradient a.G a.A ∘ y) hp hn
    a.cover.triple.q a.cover.triple.continuous_q a.cover.triple.independent a.cover.triple.perpendicular
  obtain ⟨ce,hce,Ce,hCe,heta⟩ := uniform_direction_strictness (a.G ∘ y) (sourceHessian a.G a.A ∘ y)
    (a.smooth_G.continuous.comp hy) hH (fun t ↦ a.positive_G _)
    (metricGradient a.G a.A ∘ y) hp hn a.cover.triple
  refine ⟨cs,hcs,ce,hce,Ce,hCe,?_⟩
  intro t
  obtain ⟨hge,_,hae⟩ := a.germ (y t) (a.centers_E (a.cover.center t).property)
  have hg0 := hge.self_of_nhds
  have hp0 := (metricGradient_eventuallyEq hge hae).self_of_nhds
  have hH0 := (sourceHessian_eventuallyEq hge hae).self_of_nhds
  have hspan' := hspan t
  have heta' := heta t
  dsimp only [Function.comp_def] at hspan' heta'
  rw [hg0,hp0] at hspan'
  rw [hg0,hp0,hH0] at heta'
  exact ⟨hspan',heta'⟩

end LocalCompactWaveData
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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianIntervalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section

lemma gaussian_pdf_upper_bound (mean x : ℝ) (v : ℝ≥0) :
    gaussianPDFReal mean v x ≤ (Real.sqrt (2*Real.pi*v))⁻¹ := by
  unfold gaussianPDFReal
  apply mul_le_of_le_one_right (by positivity)
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

lemma gaussian_interval_bound (mean center radius : ℝ) (hr : 0 ≤ radius)
    (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal mean v (Icc (center-radius) (center+radius)) ≤
      ENNReal.ofReal (2*radius/(Real.sqrt (2*Real.pi*v))) := by
  rw [gaussianReal_apply mean hv]
  calc
    _ ≤ ∫⁻ _ in Icc (center-radius) (center+radius),
        ENNReal.ofReal ((Real.sqrt (2*Real.pi*v))⁻¹) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (gaussian_pdf_upper_bound mean x v)
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      rw [← ENNReal.ofReal_mul' (by linarith only [hr])]
      congr 1
      ring

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianBoxBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussian_box_bound (mean center : ι → ℝ) (radius : ℝ) (hr : 0 ≤ radius)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (Measure.pi (fun i ↦ gaussianReal (mean i) v))
      (Set.pi univ (fun i ↦ Icc (center i-radius) (center i+radius))) ≤
      ENNReal.ofReal ((2*radius/(Real.sqrt (2*Real.pi*v)))^(Fintype.card ι)) := by
  classical
  rw [Measure.pi_pi]
  calc
    _ ≤ ∏ i : ι, ENNReal.ofReal (2*radius/(Real.sqrt (2*Real.pi*v))) :=
      Finset.prod_le_prod' (fun i _ ↦ gaussian_interval_bound (mean i) (center i) radius hr v hv)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ]
      rw [ENNReal.ofReal_pow (by positivity : 0 ≤ 2*radius/(Real.sqrt (2*Real.pi*v)))]

lemma gaussian_coord_ball_bound (mean center : ι → ℝ) (radius : ℝ) (hr : 0 ≤ radius)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (Measure.pi (fun i ↦ gaussianReal (mean i) v)) {z | ‖z-center‖ ≤ radius} ≤
      ENNReal.ofReal ((2*radius/(Real.sqrt (2*Real.pi*v)))^(Fintype.card ι)) := by
  apply le_trans (measure_mono ?_) (gaussian_box_bound mean center radius hr v hv)
  intro z hz i _
  have h := (norm_le_pi_norm (z-center) i).trans hz
  change |z i-center i| ≤ radius at h
  exact ⟨by linarith [(abs_le.mp h).1],by linarith [(abs_le.mp h).2]⟩

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_AffineGaussianSmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma affine_gaussian_small_ball (L : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (mean : ι → ℝ)
    (radius B : ℝ) (hr : 0 ≤ radius) (hB : 0 ≤ B) (hL : ‖L.symm.toContinuousLinearMap‖ ≤ B) :
    ((Measure.pi (fun _ : ι ↦ gaussianReal 0 1)).map (fun z ↦ mean+L z))
      {y | ‖y‖ ≤ radius} ≤
      ENNReal.ofReal ((2*(B*radius)/(Real.sqrt (2*Real.pi)))^(Fintype.card ι)) := by
  let center := L.symm (-mean)
  have hc : Continuous (fun z ↦ mean+L z) := continuous_const.add L.continuous
  rw [Measure.map_apply hc.measurable (isClosed_le continuous_norm continuous_const).measurableSet]
  have hsub : (fun z ↦ mean+L z) ⁻¹' {y | ‖y‖ ≤ radius} ⊆ {z | ‖z-center‖ ≤ B*radius} := by
    intro z hz
    have he : z-center = L.symm (mean+L z) := by simp [center,map_add,map_neg,add_comm]
    change ‖z-center‖ ≤ B*radius
    rw [he]
    apply (L.symm.toContinuousLinearMap.le_opNorm (mean+L z)).trans
    exact mul_le_mul hL hz (norm_nonneg _) hB
  apply le_trans (measure_mono hsub)
  simpa only [NNReal.coe_one,mul_one] using
    gaussian_coord_ball_bound (fun _ : ι ↦ 0) center (B*radius) (mul_nonneg hB hr) 1 one_ne_zero

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

local notation "E" => EuclideanSpace ℝ ι

lemma covarianceMatrix_posSemidef (T : F →L[ℝ] E) : (covarianceMatrix T).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff,
    ← LinearMap.isPositive_toContinuousLinearMap_iff]
  change ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (covarianceMatrix T)).IsPositive
  simpa [covarianceMatrix] using ContinuousLinearMap.isPositive_self_comp_adjoint T

lemma covarianceFactor_selfAdjoint (T : F →L[ℝ] E) : IsSelfAdjoint (covarianceFactor T) :=
  (CFC.sqrt_nonneg (covarianceMatrix T)).isSelfAdjoint.map (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ))

lemma covarianceFactor_sq (T : F →L[ℝ] E) :
    covarianceFactor T ∘L covarianceFactor T = T ∘L T.adjoint := by
  change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (CFC.sqrt (covarianceMatrix T)) *
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) (CFC.sqrt (covarianceMatrix T)) = _
  rw [← map_mul, CFC.sqrt_mul_sqrt_self _ (covarianceMatrix_posSemidef T).nonneg]
  exact (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).apply_symm_apply _

lemma covarianceFactor_inner (T : F →L[ℝ] E) (x y : E) :
    ⟪covarianceFactor T x, covarianceFactor T y⟫ = ⟪T.adjoint x, T.adjoint y⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right,
    (covarianceFactor_selfAdjoint T).adjoint_eq]
  change ⟪x, (covarianceFactor T ∘L covarianceFactor T) y⟫ = _
  rw [covarianceFactor_sq, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left]

variable [MeasurableSpace F] [BorelSpace F]

lemma gaussian_covariance_factorization (T : F →L[ℝ] E) :
    (stdGaussian F).map T = (stdGaussian E).map (covarianceFactor T) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [T.integral_id_map IsGaussian.integrable_id,
      (covarianceFactor T).integral_id_map IsGaussian.integrable_id]
    simp
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,covarianceBilin_stdGaussian,
      innerSL_apply_apply,innerSL_apply_apply,
      (covarianceFactor_selfAdjoint T).adjoint_eq]
    exact (covarianceFactor_inner T x y).symm

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianFactorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
local notation "E" => EuclideanSpace ℝ ι

lemma covarianceFactor_norm_sq (T : F →L[ℝ] E) (v : E) :
    ‖covarianceFactor T v‖^2 = ‖T.adjoint v‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using covarianceFactor_inner T v v

lemma covarianceFactor_lower (T : F →L[ℝ] E) (a : ℝ) (ha : 0 < a)
    (h : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2) (v : E) :
    Real.sqrt a * ‖v‖ ≤ ‖covarianceFactor T v‖ := by
  have hs := Real.sq_sqrt ha.le
  have hb := h v
  rw [← covarianceFactor_norm_sq T v] at hb
  nlinarith [sq_nonneg (Real.sqrt a*‖v‖-‖covarianceFactor T v‖),
    norm_nonneg (covarianceFactor T v), norm_nonneg v, Real.sqrt_nonneg a]

lemma covarianceFactor_bijective (T : F →L[ℝ] E) (a : ℝ) (ha : 0 < a)
    (h : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2) :
    Function.Bijective (covarianceFactor T) := by
  have hi : Function.Injective (covarianceFactor T) := by
    apply (covarianceFactor T).ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    change covarianceFactor T v = 0 at hv
    have hb := covarianceFactor_lower T a ha h v
    rw [hv,norm_zero] at hb
    have hz : ‖v‖ = 0 := by nlinarith [Real.sqrt_pos.mpr ha, norm_nonneg v]
    exact norm_eq_zero.mp hz
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

variable [MeasurableSpace F] [BorelSpace F]

lemma exists_gaussian_factor_equiv (T : F →L[ℝ] E) (a : ℝ) (ha : 0 < a)
    (h : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2) :
    ∃ L : E ≃L[ℝ] E,
      (stdGaussian F).map T = (stdGaussian E).map L ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt a)⁻¹ := by
  let L := (LinearEquiv.ofBijective (covarianceFactor T).toLinearMap
    (covarianceFactor_bijective T a ha h)).toContinuousLinearEquiv
  refine ⟨L, gaussian_covariance_factorization T, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hb := covarianceFactor_lower T a ha h (L.symm v)
  change Real.sqrt a*‖L.symm v‖ ≤ ‖L (L.symm v)‖ at hb
  rw [L.apply_symm_apply] at hb
  change ‖L.symm v‖ ≤ _
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr (by simpa [mul_comm] using hb)

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_EuclideanGaussianSmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma euclidean_ofLp_norm_le (v : E) : ‖WithLp.ofLp v‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  exact PiLp.norm_apply_le v i

lemma euclidean_toLp_norm_le (v : ι → ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ ((Fintype.card ι : ℝ)+1)*‖v‖ := by
  have hs : ‖WithLp.toLp 2 v‖^2 ≤ (Fintype.card ι : ℝ)*‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, (v i)^2 ≤ ∑ _ : ι, ‖v‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := norm_le_pi_norm v i
        rw [Real.norm_eq_abs] at h
        nlinarith [sq_abs (v i),abs_nonneg (v i),norm_nonneg v]
      _ = _ := by simp
  have hc : (0:ℝ) ≤ Fintype.card ι := by positivity
  have hn := norm_nonneg (WithLp.toLp 2 v)
  apply (sq_le_sq₀ hn (by positivity)).mp
  nlinarith [sq_nonneg ((Fintype.card ι : ℝ)*‖v‖),
    mul_nonneg hc (sq_nonneg ‖v‖)]

lemma euclidean_affine_small_ball (L : E ≃L[ℝ] E) (mean : E)
    (radius B : ℝ) (hr : 0 ≤ radius) (hB : 0 ≤ B)
    (hL : ‖L.symm.toContinuousLinearMap‖ ≤ B) :
    ((stdGaussian E).map (fun z ↦ mean+L z)) {y | ‖y‖ ≤ radius} ≤
      ENNReal.ofReal ((2*(B*((Fintype.card ι : ℝ)+1)*radius)/
        Real.sqrt (2*Real.pi))^(Fintype.card ι)) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)
  let K : (ι → ℝ) ≃L[ℝ] (ι → ℝ) := e.symm.trans (L.trans e)
  have hK : ‖K.symm.toContinuousLinearMap‖ ≤ B*((Fintype.card ι : ℝ)+1) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖e (L.symm (e.symm v))‖ ≤ _
    calc
      _ ≤ ‖L.symm (e.symm v)‖ := euclidean_ofLp_norm_le _
      _ ≤ ‖L.symm.toContinuousLinearMap‖*‖e.symm v‖ := L.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B*(((Fintype.card ι : ℝ)+1)*‖v‖) :=
        mul_le_mul hL (euclidean_toLp_norm_le v) (norm_nonneg _) hB
      _ = _ := by ring
  have hb := affine_gaussian_small_ball K (e mean) radius
    (B*((Fintype.card ι : ℝ)+1)) hr (by positivity) hK
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (isClosed_le continuous_norm continuous_const).measurableSet]
  rw [Measure.map_apply (by fun_prop) (isClosed_le continuous_norm continuous_const).measurableSet] at hb
  apply le_trans (measure_mono ?_) hb
  intro v hv
  change ‖e mean+K v‖ ≤ radius
  have he : e mean+K v = e (mean+L (WithLp.toLp 2 v)) := by
    simp [K,e,map_add]
  rw [he]
  exact (euclidean_ofLp_norm_le _).trans hv

variable [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma gaussian_map_small_ball (T : F →L[ℝ] E) (mean : E)
    (a radius : ℝ) (ha : 0 < a) (hr : 0 ≤ radius)
    (h : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2) :
    ((stdGaussian F).map (fun z ↦ mean+T z)) {y | ‖y‖ ≤ radius} ≤
      ENNReal.ofReal ((2*((Real.sqrt a)⁻¹*((Fintype.card ι : ℝ)+1)*radius)/
        Real.sqrt (2*Real.pi))^(Fintype.card ι)) := by
  obtain ⟨L,hLaw,hL⟩ := exists_gaussian_factor_equiv T a ha h
  have he : (stdGaussian F).map (fun z ↦ mean+T z) =
      (stdGaussian E).map (fun z ↦ mean+L z) := by
    rw [show (fun z ↦ mean+T z) = (fun z ↦ mean+z) ∘ T from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), hLaw,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he]
  exact euclidean_affine_small_ball L mean radius (Real.sqrt a)⁻¹ hr (by positivity) hL

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FiniteGaussianMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
lemma pairJetMap_apply (z : κ → ι → ℂ) (a : ι × Fin 2 → ℝ) (k : κ) :
    pairJetMap z (WithLp.toLp 2 a) k = pairLinearSum (z k) a := by
  change (∑ p : ι × Fin 2,
    (if p.2 = 0 then (z k p.1).re else -(z k p.1).im) • EuclideanSpace.proj p)
      (WithLp.toLp 2 a) = _
  simp only [sum_apply, smul_apply]
  rfl

lemma variance_gaussianMap_inner (T : EuclideanSpace ℝ (ι × Fin 2) →L[ℝ] EuclideanSpace ℝ κ)
    (v : EuclideanSpace ℝ κ) :
    Var[fun a : ι × Fin 2 → ℝ ↦ ⟪v,T (WithLp.toLp 2 a)⟫; gaussianPairs] =
      ‖T.adjoint v‖^2 := by
  have hm : (gaussianPairs (ι := ι)).map (WithLp.toLp 2) =
      stdGaussian (EuclideanSpace ℝ (ι × Fin 2)) := map_pi_eq_stdGaussian
  have hv := covarianceBilin_self (μ := (stdGaussian (EuclideanSpace ℝ (ι × Fin 2))).map T)
    IsGaussian.memLp_two_id v
  rw [covarianceBilin_map IsGaussian.memLp_two_id,covarianceBilin_stdGaussian,
    innerSL_apply_apply,real_inner_self_eq_norm_sq] at hv
  rw [variance_map (by fun_prop) (by fun_prop),← hm,
    variance_map (by fun_prop) (by fun_prop)] at hv
  exact hv.symm

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianWaveJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma pairLinearSum_eq_complex (z : ι → ℂ) (a : ι × Fin 2 → ℝ) :
    pairLinearSum z a = ∑ i, (gaussianCoefficient a i*z i).re := by
  classical
  simp only [pairLinearSum,Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.succ_ne_zero,Fin.succ_zero_eq_one,ite_true, if_true,ite_false, if_false,Fin.sum_univ_zero,add_zero,
    gaussianCoefficient,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gaussianWaveField_dual (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (a : ι × Fin 2 → ℝ)
    (x v : _root_.OAI.Yau.Jets.Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x) (N S b : ℝ) :
    Real.exp (-N*S)*(b*gaussianWaveField V a x+N⁻¹*fderiv ℝ (gaussianWaveField V a) x v) =
      pairLinearSum (fun i ↦ dualWaveCoefficient N (V i) S x b v) a := by
  classical
  let W : _root_.OAI.Yau.Jets.Coord → ℂ := fun z ↦ ∑ i, gaussianCoefficient a i*V i z
  have hW : DifferentiableAt ℝ W x := DifferentiableAt.fun_sum (fun i _ ↦ (hV i).const_mul _)
  have hd : fderiv ℝ W x v = ∑ i, gaussianCoefficient a i*fderiv ℝ (V i) x v := by
    dsimp only [W]
    rw [fderiv_fun_sum (fun i _ ↦ (hV i).const_mul _)]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [((hV i).hasFDerivAt.const_mul (gaussianCoefficient a i)).fderiv]
    rfl
  have hr := realPart_fderiv W x hW v
  change fderiv ℝ (gaussianWaveField V a) x v = _ at hr
  rw [hr,hd,pairLinearSum_eq_complex]
  simp only [gaussianWaveField,Complex.re_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dualWaveCoefficient,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,← Complex.ofReal_inv,
    zero_mul,sub_zero,add_zero]
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_SeededGaussianJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussianWaveField_differentiable (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (a : ι × Fin 2 → ℝ)
    (x : _root_.OAI.Yau.Jets.Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x) :
    DifferentiableAt ℝ (gaussianWaveField V a) x := by
  classical
  change DifferentiableAt ℝ (Complex.reCLM ∘ (fun z ↦ ∑ i, gaussianCoefficient a i*V i z)) x
  exact Complex.reCLM.differentiableAt.comp x (DifferentiableAt.fun_sum (fun i _ ↦ (hV i).const_mul _))

lemma seeded_gaussian_dual_variance (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (x v : _root_.OAI.Yau.Jets.Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x) (hseed : DifferentiableAt ℝ seed x)
    (N S b : ℝ) :
    Var[(fun a : ι × Fin 2 → ℝ ↦ Real.exp (-N*S)*(b*(seed x+gaussianWaveField V a x)+
      N⁻¹*fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x v)); gaussianPairs] =
      ∑ i, ‖dualWaveCoefficient N (V i) S x b v‖^2 := by
  let z := fun i ↦ dualWaveCoefficient N (V i) S x b v
  let mean := Real.exp (-N*S)*(b*seed x+N⁻¹*fderiv ℝ seed x v)
  have he : (fun a : ι × Fin 2 → ℝ ↦ Real.exp (-N*S)*(b*(seed x+gaussianWaveField V a x)+
      N⁻¹*fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x v)) =
      fun a ↦ mean+pairLinearSum z a := by
    funext a
    rw [fderiv_fun_add hseed (gaussianWaveField_differentiable V a x hV),add_apply]
    have h := gaussianWaveField_dual V a x v hV N S b
    change _ = mean+pairLinearSum z a
    rw [← h]
    dsimp [mean]
    ring
  rw [he]
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : ι × Fin 2 ↦ gaussianReal 0 1))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hc : Continuous (pairLinearSum z) := by
    unfold pairLinearSum
    fun_prop
  rw [variance_const_add hc.aestronglyMeasurable]
  exact variance_pairLinearSum _

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma normalizedRealJet_inner (f : _root_.OAI.Yau.Jets.Coord → ℝ) (N S : ℝ) (x : _root_.OAI.Yau.Jets.Coord) (v : JetSpace) :
    ⟪v,normalizedRealJet f N S x⟫ =
      Real.exp (-N*S)*(v 0*f x+N⁻¹*fderiv ℝ f x (Fin.tail (WithLp.ofLp v))) := by
  have he : Fin.tail (WithLp.ofLp v) = ∑ i : Fin 4, (v i.succ) • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply,Fin.tail]
  rw [he,map_sum]
  simp only [map_smul,smul_eq_mul]
  simp only [normalizedRealJet,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring

lemma gaussianWaveField_normalizedJet (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (N S : ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (hV : ∀ i, DifferentiableAt ℝ (V i) x) (a : ι × Fin 2 → ℝ) :
    normalizedRealJet (gaussianWaveField V a) N S x =
      pairJetMap (jetWaveCoefficients V N S x) (WithLp.toLp 2 a) := by
  ext k
  rw [pairJetMap_apply]
  refine Fin.cases ?_ (fun j ↦ ?_) k
  · simpa [normalizedRealJet,jetWaveCoefficients] using
      gaussianWaveField_dual V a x 0 hV N S 1
  · simpa [normalizedRealJet,jetWaveCoefficients,mul_assoc] using
      gaussianWaveField_dual V a x (Pi.single j 1) hV N S 0

lemma normalizedRealJet_add (f g : _root_.OAI.Yau.Jets.Coord → ℝ) (N S : ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    normalizedRealJet (fun y ↦ f y+g y) N S x =
      normalizedRealJet f N S x+normalizedRealJet g N S x := by
  ext k
  refine Fin.cases ?_ (fun j ↦ ?_) k
  · simp [normalizedRealJet,mul_add]
  · simp [normalizedRealJet,fderiv_fun_add hf hg,mul_add]

lemma seeded_gaussian_jet_eq (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N S : ℝ) (x : _root_.OAI.Yau.Jets.Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x)
    (hs : DifferentiableAt ℝ seed x) (a : ι × Fin 2 → ℝ) :
    normalizedRealJet (fun y ↦ seed y+gaussianWaveField V a y) N S x =
      normalizedRealJet seed N S x+
        pairJetMap (jetWaveCoefficients V N S x) (WithLp.toLp 2 a) := by
  rw [normalizedRealJet_add _ _ _ _ _ hs (gaussianWaveField_differentiable V a x hV),
    gaussianWaveField_normalizedJet V N S x hV]

lemma seeded_gaussian_jet_law (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N S : ℝ) (x : _root_.OAI.Yau.Jets.Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x)
    (hs : DifferentiableAt ℝ seed x) :
    (gaussianPairs (ι := ι)).map (fun a ↦
      normalizedRealJet (fun y ↦ seed y+gaussianWaveField V a y) N S x) =
      (stdGaussian (EuclideanSpace ℝ (ι × Fin 2))).map
        (fun z ↦ normalizedRealJet seed N S x+pairJetMap (jetWaveCoefficients V N S x) z) := by
  simp_rw [seeded_gaussian_jet_eq V seed N S x hV hs]
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma seeded_gaussian_jet_variance (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N S : ℝ) (x : _root_.OAI.Yau.Jets.Coord) (hV : ∀ i, DifferentiableAt ℝ (V i) x)
    (hs : DifferentiableAt ℝ seed x) (v : JetSpace) :
    Var[fun a : ι × Fin 2 → ℝ ↦
      ⟪v,normalizedRealJet (fun y ↦ seed y+gaussianWaveField V a y) N S x⟫; gaussianPairs] =
      ‖(pairJetMap (jetWaveCoefficients V N S x)).adjoint v‖^2 := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by
    unfold gaussianPairs
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  simp_rw [seeded_gaussian_jet_eq V seed N S x hV hs,inner_add_right]
  rw [variance_const_add (by fun_prop)]
  exact variance_gaussianMap_inner _ v

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

theorem lattice_wave_estimates (d : SourceCompactFrameCover g S D)
    (b : TripleSourceWaveData g w S (coverSourceCenter d) d.triple m J K k0)
    (hUD : U ⊆ D) :
    ∀ᶠ n : ℕ in atTop, ∀ (z : SourceGrid U n) (j : Fin 3),
      ContDiff ℝ ∞ (latticeWave d b hUD n z j) ∧ HasCompactSupport (latticeWave d b hUD n z j) ∧
      tsupport (latticeWave d b hUD n z j) ⊆
        {x | sourceEuclideanNorm (x-scaledLatticePoint n z) ≤ b.R*(n:ℝ)^(-1/3:ℝ)} ∧
      ∀ x : _root_.OAI.Yau.Jets.Coord,
        (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (latticeWave d b hUD n z j) x‖ ≤
          b.Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S x-b.c*(n:ℝ)*(sourceEuclideanNorm (x-scaledLatticePoint n z))^2)) ∧
        DerivativeBound k0 (fun x ↦ sourceWeightedOperator g w (latticeWave d b hUD n z j) x +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*latticeWave d b hUD n z j x) x
            (b.Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x)) := by
  filter_upwards [b.estimates] with n hn
  intro z j
  simpa only [latticeWave,latticeFrame_center] using hn (latticeFrame d hUD n z,j)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma lattice_scale_pos {n : ℕ} (hn : 0 < n) : 0 < (n:ℝ)^(-1/2:ℝ) :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem finite_source_grid {U : Set _root_.OAI.Yau.Jets.Coord} (hU : Bornology.IsBounded U)
    {n : ℕ} (hn : 0 < n) : Finite (SourceGrid U n) := by
  obtain ⟨B,hB,hbound⟩ := hU.exists_pos_norm_le
  let r : ℝ := (n:ℝ)^(-1/2:ℝ)
  have hr : 0 < r := lattice_scale_pos hn
  let M : ℤ := ⌈B/r⌉
  have hcoords (z : SourceGrid U n) (i : Fin 4) : z.val i ∈ Icc (-M) M := by
    have hi := (norm_le_pi_norm (scaledLatticePoint n z) i).trans (hbound _ z.property)
    change |r*(z.val i:ℝ)| ≤ B at hi
    rw [abs_mul,abs_of_pos hr] at hi
    have ha : |(z.val i:ℝ)| ≤ B/r := (le_div_iff₀ hr).mpr (by nlinarith)
    have hM : B/r ≤ (M:ℝ) := Int.le_ceil _
    have hpair := abs_le.mp (ha.trans hM)
    constructor
    · exact_mod_cast hpair.1
    · exact_mod_cast hpair.2
  let f : SourceGrid U n → (Fin 4 → Icc (-M) M) := fun z i ↦ ⟨z.val i,hcoords z i⟩
  apply Finite.of_injective f
  intro z w h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

theorem rounded_lattice_distance {n : ℕ} (hn : 0 < n) (x : _root_.OAI.Yau.Jets.Coord) :
    sourceEuclideanNorm (scaledLatticePoint n (roundedLatticeIndex n x)-x) ≤
      2*(n:ℝ)^(-1/2:ℝ) := by
  let r : ℝ := (n:ℝ)^(-1/2:ℝ)
  have hr : 0 < r := lattice_scale_pos hn
  have hb : ‖scaledLatticePoint n (roundedLatticeIndex n x)-x‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg hr.le).mpr
    intro i
    have h1 := Int.floor_le (x i/r)
    have h2 := Int.lt_floor_add_one (x i/r)
    have h1' := mul_le_mul_of_nonneg_left h1 hr.le
    have h2' := mul_lt_mul_of_pos_left h2 hr
    have he : r*(x i/r) = x i := by field_simp
    rw [he] at h1' h2'
    change |r*(⌊x i/r⌋:ℝ)-x i| ≤ r
    apply abs_le.mpr
    constructor <;> nlinarith
  exact (sourceEuclideanNorm_le _).trans (by dsimp [r] at hb ⊢ <;> linarith)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeDirectionalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
noncomputable section

lemma norm_unitDirection_le (v : _root_.OAI.Yau.Jets.Coord) : ‖unitDirection v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [unitDirection,hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  simp only [unitDirection,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  exact le_rfl

lemma directional_rounding_error {n : ℕ} (hn : 0 < n) (x : _root_.OAI.Yau.Jets.Coord) (K : ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    ‖scaledLatticePoint n (directionalLatticeIndex n x K v)-
      (x+(K*(n:ℝ)^(-1/2:ℝ)) • unitDirection v)‖ ≤ 2*(n:ℝ)^(-1/2:ℝ) :=
  (norm_le_sourceEuclideanNorm _).trans (rounded_lattice_distance hn _)

lemma directional_center_distance {n : ℕ} (hn : 0 < n) (x : _root_.OAI.Yau.Jets.Coord) (K : ℝ) (hK : 0 ≤ K) (v : _root_.OAI.Yau.Jets.Coord) :
    ‖scaledLatticePoint n (directionalLatticeIndex n x K v)-x‖ ≤ (K+2)*(n:ℝ)^(-1/2:ℝ) := by
  let z := x+(K*(n:ℝ)^(-1/2:ℝ)) • unitDirection v
  have h := norm_sub_le_norm_sub_add_norm_sub (scaledLatticePoint n (directionalLatticeIndex n x K v)) z x
  have hz : ‖z-x‖ ≤ K*(n:ℝ)^(-1/2:ℝ) := by
    simp only [z,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hK (lattice_scale_pos hn).le)]
    exact (mul_le_mul_of_nonneg_left (norm_unitDirection_le v)
      (mul_nonneg hK (lattice_scale_pos hn).le)).trans_eq (mul_one _)
  have hr := directional_rounding_error hn x K v
  dsimp [z] at h hz
  nlinarith

lemma directional_center_mem {U : Set _root_.OAI.Yau.Jets.Coord} {n : ℕ} (hn : 0 < n)
    (x : _root_.OAI.Yau.Jets.Coord) (K : ℝ) (hK : 0 ≤ K) (v : _root_.OAI.Yau.Jets.Coord)
    (hball : closedBall x ((K+2)*(n:ℝ)^(-1/2:ℝ)) ⊆ U) :
    scaledLatticePoint n (directionalLatticeIndex n x K v) ∈ U :=
  hball (by simpa only [mem_closedBall,dist_eq_norm] using directional_center_distance hn x K hK v)

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

theorem lattice_eta_bounds {U : Set _root_.OAI.Yau.Jets.Coord} (hUD : U ⊆ D) :
    ∃ e > 0, ∃ E > 0, ∀ n (z : SourceGrid U n) j,
      e ≤ a.latticeEta hUD n z j ∧ a.latticeEta hUD n z j ≤ E := by
  obtain ⟨_,_,e,he,E,hE,hb⟩ := a.original_direction_bounds
  refine ⟨e,he,E,hE,?_⟩
  intro n z j
  exact (hb (latticeFrame a.cover hUD n z)).2 j

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

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_energy_lower_bound (hUD : U ⊆ D) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), ∀ x ∈ Q, ∀ b v,
      c/(n:ℝ)*(b^2+‖v‖^2) ≤ a.latticeEnergy hUD n hfin x b v := by
  obtain ⟨mu,hmu,B,hB,hgeom⟩ := a.original_covariance_geometry
  obtain ⟨e,he,E,hE,heta⟩ := a.lattice_eta_bounds hUD
  let R : ℝ := (2*B+2)/mu
  have hR : 0 < R := by dsimp [R] <;> positivity
  let L := R+2
  have hL : 0 < L := by dsimp [L] <;> linarith
  have hlarge : 2*B+1 ≤ R*mu := by dsimp [R]; rw [div_mul_cancel₀ _ hmu.ne']; linarith
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,s,hs,C,hC,hjets⟩ := a.lattice_logarithmic_jet_estimates hUD L hL
  let F := B+E*B*L+Cr
  have hF : 0 ≤ F := by dsimp [F] <;> positivity
  let kappa := e^2/(2*(e+F+1)^2)
  have hkappa : 0 < kappa := by dsimp [kappa] <;> positivity
  obtain ⟨r,hr,hinner⟩ := compact_inner_ball hQ hU hQU
  refine ⟨s^2*kappa/2,by positivity,?_⟩
  filter_upwards [hjets,eventually_nat_frequency (half_scale_eventually L 1 r hr),
    eventually_nat_frequency (half_scale_eventually (2*Cr) 1 e he)] with n hj hn hsmall
  have hn1 : 1 ≤ n := by exact_mod_cast hn.1
  have hnpos : 0 < n := by omega
  have hN : 0 < (n:ℝ) := by exact_mod_cast hnpos
  let h := (n:ℝ)^(-1/2:ℝ)
  have hh : 0 < h := lattice_scale_pos hnpos
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn.1 (by norm_num)
  let : Finite (SourceGrid U n) := finite_source_grid hUb hnpos
  let hfin : Fintype (SourceGrid U n) := Fintype.ofFinite _
  refine ⟨hfin,?_⟩
  intro x hx b v
  have hxD := hUD (hQU hx)
  have hball : closedBall x (L*h) ⊆ U := (closedBall_subset_closedBall hn.2.1).trans (hinner x hx)
  let z (v : _root_.OAI.Yau.Jets.Coord) : SourceGrid U n := ⟨directionalLatticeIndex n x R v,
    directional_center_mem hnpos x R hR.le v hball⟩
  let V (v : _root_.OAI.Yau.Jets.Coord) := latticeWave a.cover a.beams hUD n (z v) 0
  let yy (v : _root_.OAI.Yau.Jets.Coord) := scaledLatticePoint n (z v)
  have hdist (v : _root_.OAI.Yau.Jets.Coord) : ‖x-yy v‖ ≤ L*h := by
    rw [norm_sub_rev]
    exact directional_center_distance hnpos x R hR.le v
  have hjet (v : _root_.OAI.Yau.Jets.Coord) := hj (z v) 0 x (hdist v)
  let Rp := b+(normalizedLogJet n (V v) x v).re
  let Rm := b+(normalizedLogJet n (V (-v)) x v).re
  let pp := g (yy v) (x-yy v) v
  let pm := g (yy (-v)) (x-yy (-v)) v
  let ep := a.latticeEta hUD n (z v) 0
  let em := a.latticeEta hUD n (z (-v)) 0
  have hgp := hgeom (yy v) (hUD (z v).property)
  have hgm := hgeom (yy (-v)) (hUD (z (-v)).property)
  have hpp : pp ≤ -h*‖v‖ := rounded_positive_pairing (g (yy v)) mu B R h hmu hB.le hR.le hh.le
    hgp.1 hgp.2.2 hlarge x (yy v) v (directional_rounding_error hnpos x R v)
  have hpm : h*‖v‖ ≤ pm := by
    have hh' := rounded_positive_pairing (g (yy (-v))) mu B R h hmu hB.le hR.le hh.le
      hgm.1 hgm.2.2 hlarge x (yy (-v)) (-v) (directional_rounding_error hnpos x R (-v))
    simp only [map_neg,norm_neg] at hh'
    dsimp [pm]
    linarith
  have herr (u : _root_.OAI.Yau.Jets.Coord) : |(b+(normalizedLogJet n (V u) x v).re)-
      ((b+fderiv ℝ S x v)-a.latticeEta hUD n (z u) 0*g (yy u) (x-yy u) v)| ≤ Cr*h^2*‖v‖ := by
    have hh' := ((hjet u).2.2.2.2.2 v).1
    have heq : Cr/(n:ℝ)*‖v‖ = Cr*h^2*‖v‖ := by dsimp [h]; rw [half_scale_square hN]; ring
    rw [heq] at hh'
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hdiff : e*h*‖v‖ ≤ Rp-Rm := opposite_real_products (b+fderiv ℝ S x v)
    Rp Rm ep em pp pm h ‖v‖ e Cr hh.le (norm_nonneg _) he.le
    (heta n (z v) 0).1 (heta n (z (-v)) 0).1 hpp hpm (herr v) (herr (-v)) hsmall.2.1
  have hprod : |ep*pp| ≤ E*B*L*‖v‖ := by
    have hpabs := (bilinear_pairing_bound (g (yy v)) (x-yy v) v).trans
      (show ‖g (yy v)‖*‖x-yy v‖*‖v‖ ≤ B*(L*h)*‖v‖ by
        gcongr
        · exact hgp.1
        · exact hdist v)
    have hepos : 0 ≤ ep := he.le.trans (heta n (z v) 0).1
    rw [abs_mul,abs_of_nonneg hepos]
    calc
      ep*|pp| ≤ E*(B*(L*h)*‖v‖) := mul_le_mul (heta n (z v) 0).2 hpabs (abs_nonneg _) hE.le
      _ ≤ E*(B*L*‖v‖) := by
        gcongr
        simpa using mul_le_mul_of_nonneg_left hh1 hL.le
      _ = _ := by ring
  have hSv : |fderiv ℝ S x v| ≤ B*‖v‖ :=
    ((fderiv ℝ S x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hgeom x hxD).2.1 (norm_nonneg v))
  have hErr : Cr*h^2*‖v‖ ≤ Cr*‖v‖ := by
    have hh2 := pow_le_pow_left₀ hh.le hh1 2
    nlinarith [mul_nonneg hCr.le (norm_nonneg v)]
  have hlog : |(normalizedLogJet n (V v) x v).re| ≤ F*‖v‖ := by
    have hpR := abs_le.mp ((herr v).trans hErr)
    have hpP := abs_le.mp hprod
    have hpS := abs_le.mp hSv
    dsimp [F,Rp,ep,pp] at *
    apply abs_le.mpr
    constructor <;> nlinarith
  have hb : |b| ≤ |Rp|+F*‖v‖ := by
    have ht := norm_sub_le (b+(normalizedLogJet n (V v) x v).re) (normalizedLogJet n (V v) x v).re
    have ht' : |b| ≤ |Rp|+|(normalizedLogJet n (V v) x v).re| := by simpa only [add_sub_cancel_right,Real.norm_eq_abs] using ht
    exact ht'.trans (add_le_add le_rfl hlog)
  have hpair := paired_products_control b ‖v‖ Rp Rm h e F (norm_nonneg _) hh hh1 he hF hdiff hb
  let f (i : SourceGrid U n × Fin 3) := dualWaveCoefficient n
    (latticeWave a.cover a.beams hUD n i.1 i.2) (S x) x b v
  have hcoef (u : _root_.OAI.Yau.Jets.Coord) : s*|b+(normalizedLogJet n (V u) x v).re| ≤ ‖f (z u,0)‖ :=
    (mul_le_mul_of_nonneg_right (hjet u).2.2.2.2.1.1 (abs_nonneg _)).trans
      (real_log_product_le_coefficient n (V u) (S x) x b v (hjet u).2.2.2.1)
  have henergy := two_coefficient_energy f (z v,0) (z (-v),0) s Rp Rm hs.le (hcoef v) (hcoef (-v))
  have hpair' := mul_le_mul_of_nonneg_left hpair (sq_nonneg s)
  have hhbound := hpair'.trans henergy
  change s^2*(kappa*h^2*(b^2+‖v‖^2)) ≤ 2*a.latticeEnergy hUD n hfin x b v at hhbound
  calc
    _ = (s^2*(kappa*h^2*(b^2+‖v‖^2)))/2 := by dsimp [h]; rw [half_scale_square hN]; ring
    _ ≤ _ := (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by linarith)

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeCovariance2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma variance_latticeRandomDual (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (x : _root_.OAI.Yau.Jets.Coord) (b : ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    letI := hfin
    Var[a.latticeRandomDual hUD n hfin x b v; gaussianPairs] = a.latticeEnergy hUD n hfin x b v := by
  let := hfin
  exact variance_pairLinearSum _

theorem lattice_covariance_lower_bound (hUD : U ⊆ D) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), ∀ x ∈ Q, ∀ b v,
      letI := hfin
      c/(n:ℝ)*(b^2+‖v‖^2) ≤ Var[a.latticeRandomDual hUD n hfin x b v; gaussianPairs] := by
  obtain ⟨c,hc,hb⟩ := a.lattice_energy_lower_bound hUD hU hUb hQ hQU
  refine ⟨c,hc,?_⟩
  filter_upwards [hb] with n hn
  obtain ⟨hfin,hbound⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx b v
  rw [a.variance_latticeRandomDual]
  exact hbound x hx b v

theorem euclidean_lattice_covariance_lower_bound (hUD : U ⊆ D) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), ∀ x ∈ Q, ∀ b v,
      letI := hfin
      c/(n:ℝ)*(b^2+∑ i : Fin 4, (v i)^2) ≤ Var[a.latticeRandomDual hUD n hfin x b v; gaussianPairs] := by
  obtain ⟨c,hc,hb⟩ := a.lattice_covariance_lower_bound hUD hU hUb hQ hQU
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℕ)] with n hn hn1
  obtain ⟨hfin,hbound⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx b v
  apply le_trans _ (hbound x hx b v)
  have hcoord (i : Fin 4) : (v i)^2 ≤ ‖v‖^2 := by
    have hh := norm_le_pi_norm v i
    change |v i| ≤ ‖v‖ at hh
    nlinarith [sq_abs (v i),norm_nonneg v,abs_nonneg (v i)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) ↦ hcoord i)
  norm_num at hsum
  have hh : b^2+∑ i : Fin 4, (v i)^2 ≤ 4*(b^2+‖v‖^2) := by nlinarith [sq_nonneg b]
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ c/(4*(n:ℝ)))
  first | (convert hh' using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh'.trans (le_of_eq (by ring)))

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma variance_latticeSeededRandomDual (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (seed : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) (hseed : DifferentiableAt ℝ seed x)
    (hV : ∀ z j, DifferentiableAt ℝ (latticeWave a.cover a.beams hUD n z j) x)
    (b : ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    letI := hfin
    Var[a.latticeSeededRandomDual hUD n hfin seed x b v; gaussianPairs] =
      a.latticeEnergy hUD n hfin x b v := by
  let := hfin
  exact seeded_gaussian_dual_variance
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
    seed x v (fun i ↦ hV i.1 i.2) hseed (n:ℝ) (S x) b

theorem actual_lattice_covariance_lower_bound (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ (seed : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord), x ∈ Q → DifferentiableAt ℝ seed x → ∀ (b : ℝ) (v : _root_.OAI.Yau.Jets.Coord),
      c/(n:ℝ)*(b^2+∑ i : Fin 4, (v i)^2) ≤
        Var[a.latticeSeededRandomDual hUD n hfin seed x b v; gaussianPairs] := by
  obtain ⟨c,hc,hb⟩ := a.euclidean_lattice_covariance_lower_bound hUD hU hUb hQ hQU
  refine ⟨c,hc,?_⟩
  filter_upwards [hb,lattice_wave_estimates a.cover a.beams hUD] with n hn hs
  obtain ⟨hfin,hbound⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro seed x hx hseed b v
  have hV : ∀ z j, DifferentiableAt ℝ (latticeWave a.cover a.beams hUD n z j) x :=
    fun z j ↦ ((hs z j).1.differentiable (by simp)).differentiableAt
  rw [a.variance_latticeSeededRandomDual hUD n hfin seed x hseed hV]
  have hb := hbound x hx b v
  rw [a.variance_latticeRandomDual] at hb
  exact hb

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeGaussianSmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal RealInnerProductSpace
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma latticeSeededJet_inner (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (seed : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) (v : JetSpace)
    (coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ) :
    ⟪v,a.latticeSeededJet hUD n hfin seed x coeff⟫ =
      a.latticeSeededRandomDual hUD n hfin seed x (v 0) (Fin.tail (WithLp.ofLp v)) coeff := by
  let := hfin
  unfold latticeSeededJet latticeSeededRandomDual
  exact normalizedRealJet_inner
    (fun z ↦ seed z + gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
      coeff z) (n : ℝ) (S x) x v

theorem actual_lattice_gaussian_small_ball_oai (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ (seed : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord), x ∈ Q → DifferentiableAt ℝ seed x →
      ∀ r : ℝ, 0 ≤ r →
        (gaussianPairs.map (a.latticeSeededJet hUD n hfin seed x)) {y | ‖y‖ ≤ r} ≤
          ENNReal.ofReal ((12*(Real.sqrt (c/(n:ℝ)))⁻¹*r/Real.sqrt (2*Real.pi))^5) := by
  obtain ⟨c,hc,hcov⟩ := a.actual_lattice_covariance_lower_bound hUD hU hUb hQ hQU
  refine ⟨c,hc,?_⟩
  filter_upwards [hcov,lattice_wave_estimates a.cover a.beams hUD,
    eventually_gt_atTop (0:ℕ)] with n hn hw hnpos
  obtain ⟨hfin,hbound⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro seed x hx hs r hr
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV : ∀ i, DifferentiableAt ℝ (V i) x := fun i ↦
    ((hw i.1 i.2).1.differentiable (by simp)).differentiableAt
  have hb (v : JetSpace) : c/(n:ℝ)*‖v‖^2 ≤
      ‖(pairJetMap (jetWaveCoefficients V n (S x) x)).adjoint v‖^2 := by
    have h := hbound seed x hx hs (v 0) (Fin.tail (WithLp.ofLp v))
    have he : (fun coeff ↦ ⟪v,a.latticeSeededJet hUD n hfin seed x coeff⟫) =
        a.latticeSeededRandomDual hUD n hfin seed x (v 0) (Fin.tail (WithLp.ofLp v)) := by
      funext coeff
      exact a.latticeSeededJet_inner hUD n hfin seed x v coeff
    rw [← he] at h
    change c/(n:ℝ)*((v 0)^2+∑ i : Fin 4, (v i.succ)^2) ≤
      Var[fun coeff ↦ ⟪v,normalizedRealJet (fun y ↦ seed y+gaussianWaveField V coeff y)
        (n:ℝ) (S x) x⟫; gaussianPairs] at h
    rw [seeded_gaussian_jet_variance V seed n (S x) x hV hs v] at h
    simpa only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ] using h
  have hl := seeded_gaussian_jet_law V seed n (S x) x hV hs
  change gaussianPairs.map (a.latticeSeededJet hUD n hfin seed x) = _ at hl
  rw [hl]
  have h := gaussian_map_small_ball (pairJetMap (jetWaveCoefficients V n (S x) x))
    (normalizedRealJet seed n (S x) x) (c/(n:ℝ)) r (by positivity) hr hb
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  congr 2
  ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball_oai := @OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball_oai
