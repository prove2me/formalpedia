-- Prove2me | solution 1 for OAI.Yau.Geometry.construct_triple_source_waves
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:25:01.946627+00:00
-- url     : https://prove2.me/submissions/fc6ebbdf-cb99-462c-90fb-7a501de71012

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
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_constructed_coordinate_wave_estimates

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothJet
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

lemma coordPartial_contDiff {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (coordPartial i f) :=
  (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

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

lemma pulledForm_smooth (g : E → E →L[ℝ] E →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (Function.uncurry (pulledForm g)) := by
  let J : QuadParam E × E → E →L[ℝ] E := fun z ↦ fderiv ℝ (rawQuadratic z.1) z.2
  have hJ : ContDiff ℝ ∞ J :=
    smooth_spatial_fderiv (rawQuadratic (E := E)) rawQuadratic_smooth
  have hG : ContDiff ℝ ∞ (fun z : QuadParam E × E ↦ g (rawQuadratic z.1 z.2)) :=
    hg.comp rawQuadratic_smooth
  let L : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E E ℝ).flip
  have hL₀ : ContDiff ℝ ∞ (fun A : E →L[ℝ] E ↦ L A) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E →L[ℝ] E)
      (F := (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) L
  have hL : ContDiff ℝ ∞ (fun z : QuadParam E × E ↦
      (ContinuousLinearMap.compL ℝ E E ℝ).flip (J z)) :=
    hL₀.comp hJ
  have hC : ContDiff ℝ ∞ (fun z : QuadParam E × E ↦
      ((ContinuousLinearMap.compL ℝ E E ℝ).flip (J z)).comp (g (rawQuadratic z.1 z.2))) :=
    hL.clm_comp hG
  exact hC.clm_comp hJ

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

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalSpatialJet
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

variable [CompleteSpace E]

theorem inversePulledForm_smooth_at (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (p : QuadParam E) (x : E)
    (m : E ≃L[ℝ] E →L[ℝ] ℝ) (hm : pulledForm g p x = m.toContinuousLinearMap) :
    ContDiffAt ℝ ∞ (Function.uncurry (inversePulledForm g)) (p,x) := by
  have hi : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E))
      (pulledForm g p x) := by
    rw [hm]
    exact contDiffAt_map_inverse m
  exact hi.comp (p,x) (pulledForm_smooth g hg).contDiffAt

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TransformedDensity
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

lemma coordDet_smooth : ContDiff ℝ ∞ coordDet := by
  have hdet : coordDet = fun J : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord ↦
      ∑ σ : Equiv.Perm (Fin 4), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, J (Pi.single i 1) (σ i) := by
    funext J
    exact Matrix.det_apply' _
  rw [hdet]
  apply ContDiff.sum
  intro sigma _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (ContinuousLinearMap.proj (sigma i) : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).contDiff.comp
    (contDiff_id.clm_apply contDiff_const)

lemma coordDet_equiv_ne_zero (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) : coordDet J.toContinuousLinearMap ≠ 0 := by
  change (LinearMap.toMatrix' J.toLinearEquiv.toLinearMap).det ≠ 0
  rw [LinearMap.det_toMatrix']
  exact J.toLinearEquiv.isUnit_det'.ne_zero

lemma chartDensity_pos (w : _root_.OAI.Yau.Jets.Coord → ℝ) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hw : 0 < w (rawQuadratic p x)) (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap) :
    0 < chartDensity w p x := by
  unfold chartDensity
  rw [hJ]
  exact mul_pos hw (abs_pos.mpr (coordDet_equiv_ne_zero J))

theorem chartDensity_smooth_at (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap) :
    ContDiffAt ℝ ∞ (Function.uncurry (chartDensity w)) (p,x) := by
  have hdet := coordDet_smooth.comp (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth)
  have hn : coordDet (fderiv ℝ (rawQuadratic p) x) ≠ 0 := by
    rw [hJ]; exact coordDet_equiv_ne_zero J
  exact (hw.comp rawQuadratic_smooth).contDiffAt.mul (hdet.contDiffAt.abs hn)

lemma pulledForm_positive (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap) :
    ∀ v, v ≠ 0 → 0 < pulledForm g p x v v := by
  intro v hv
  change 0 < g (rawQuadratic p x) (fderiv ℝ (rawQuadratic p) x v) (fderiv ℝ (rawQuadratic p) x v)
  rw [hJ]
  exact hp (J v) (by intro hz; exact hv (J.injective (by simpa using hz)))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransformedDrift
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

lemma chartPrincipal_smooth_at (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i j : Fin 4) : ContDiffAt ℝ ∞ (Function.uncurry (chartPrincipal g i j)) (p,x) := by
  have hpos := pulledForm_positive g p x hp J hJ
  exact (ContinuousLinearMap.proj i : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).contDiff.contDiffAt.comp (p,x)
    ((inversePulledForm_smooth_at g hg p x
      (positiveMetricEquiv (pulledForm g p x) hpos) rfl).clm_apply contDiffAt_const)

lemma chartDrift_smooth_at (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v) (hwpos : 0 < w (rawQuadratic p x))
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (j : Fin 4) : ContDiffAt ℝ ∞ (Function.uncurry (chartDrift g w j)) (p,x) := by
  have hW := chartDensity_smooth_at w hw p x J hJ
  apply (hW.inv (ne_of_gt (chartDensity_pos w p x hwpos J hJ))).mul
  apply ContDiffAt.sum
  intro i _
  exact (smooth_spatial_fderiv_at (chartFlux g w i j) p x
    (hW.mul (chartPrincipal_smooth_at g hg p x hp J hJ i j))).clm_apply contDiffAt_const

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_SmoothWaveOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma waveExp_contDiff {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi) (N : ℝ) :
    ContDiff ℝ ∞ (waveExp phi N) := (contDiff_const.mul hp).cexp

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedCoordinateOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma coordPartial_mul_at (f u : Coord → ℂ) (x : Coord)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (i : Fin 4) :
    coordPartial i (fun z ↦ f z * u z) x =
      coordPartial i f x * u x + f x * coordPartial i u x := by
  unfold coordPartial
  rw [fderiv_fun_mul hf hu]
  simp [smul_eq_mul]
  ring

theorem weightedCoordinateOperator_eq (W : Coord → ℂ)
    (a : Fin 4 → Fin 4 → Coord → ℂ) (u : Coord → ℂ) (x : Coord)
    (hW : W x ≠ 0)
    (hflux : ∀ i j, DifferentiableAt ℝ (fun z ↦ W z * a i j z) x)
    (hu : ∀ j, DifferentiableAt ℝ (coordPartial j u) x) :
    weightedCoordinateOperator W a u x = smoothSecondOrder a (densityDrift W a) u x := by
  unfold weightedCoordinateOperator
  simp_rw [coordPartial_mul_at _ _ x (hflux _ _) (hu _)]
  simp only [Finset.sum_add_distrib, mul_add]
  have hfirst : (W x)⁻¹ * (∑ i, ∑ j,
      coordPartial i (fun z ↦ W z * a i j z) x * coordPartial j u x) =
      ∑ j, densityDrift W a j x * coordPartial j u x := by
    rw [Finset.sum_comm]
    simp only [densityDrift, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hsecond : (W x)⁻¹ * (∑ i, ∑ j,
      W x * a i j x * coordPartial i (coordPartial j u) x) =
      ∑ i, ∑ j, a i j x * coordPartial i (coordPartial j u) x := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hfirst,hsecond]
  simp only [smoothSecondOrder]
  ring

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartOperatorIdentity
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

lemma inverse_form_pair (G : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < G v v) (a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    G (ContinuousLinearMap.inverse G a) v = a v := by
  have hi : ContinuousLinearMap.inverse G = (positiveMetricEquiv G hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv G hp)
  change positiveMetricEquiv G hp (ContinuousLinearMap.inverse G a) v = _
  rw [hi, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

lemma coordPartial_ofReal_at (f : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ (f z : ℂ)) x = (fderiv ℝ f x (Pi.single i 1) : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x (Pi.single i 1) = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

lemma densityDrift_chart (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hF : ∀ i j, DifferentiableAt ℝ (chartFlux g w i j p) x) (j : Fin 4) :
    densityDrift (fun z ↦ (chartDensity w p z : ℂ))
      (fun i j ↦ complexPrincipal g i j p) j x = complexDrift g w j p x := by
  have he (i j : Fin 4) : (fun z ↦ (chartDensity w p z : ℂ) * complexPrincipal g i j p z) =
      fun z ↦ (chartFlux g w i j p z : ℂ) := by
    funext z
    simp [chartFlux,complexPrincipal,Complex.ofReal_mul]
  unfold densityDrift
  simp_rw [he,coordPartial_ofReal_at _ x (hF _ _)]
  simp [complexDrift,chartDrift,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_sum]

theorem actual_chart_weighted_operator
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v) (hwpos : 0 < w (rawQuadratic p x))
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) :
    weightedCoordinateOperator (fun z ↦ (chartDensity w p z : ℂ))
      (fun i j ↦ complexPrincipal g i j p) u x =
      smoothSecondOrder (fun i j ↦ complexPrincipal g i j p) (fun j ↦ complexDrift g w j p) u x := by
  have hF (i j : Fin 4) : DifferentiableAt ℝ (chartFlux g w i j p) x := by
    have h := ((chartDensity_smooth_at w hw p x J hJ).mul
      (chartPrincipal_smooth_at g hg p x hp J hJ i j)).comp x
        (contDiffAt_const.prodMk contDiffAt_id)
    exact h.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hFc (i j : Fin 4) : DifferentiableAt ℝ
      (fun z ↦ (chartDensity w p z : ℂ) * complexPrincipal g i j p z) x := by
    have he : (fun z ↦ (chartDensity w p z : ℂ) * complexPrincipal g i j p z) =
        Complex.ofRealCLM ∘ chartFlux g w i j p := by
      funext z
      simp [chartFlux,complexPrincipal]
    rw [he]
    exact Complex.ofRealCLM.differentiableAt.comp x (hF i j)
  rw [weightedCoordinateOperator_eq _ _ _ x
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (chartDensity_pos w p x hwpos J hJ))) hFc
    (fun j ↦ (coordPartial_contDiff hu j).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
  unfold smoothSecondOrder
  simp_rw [densityDrift_chart g w p x hF]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ContravariantPullback
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

theorem inversePulledForm_transform
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) :
    inversePulledForm g p x a =
      J.symm (ContinuousLinearMap.inverse (g (rawQuadratic p x))
        (a.comp J.symm.toContinuousLinearMap)) := by
  apply positive_metric_injective (pulledForm g p x) (pulledForm_positive g p x hp J hJ)
  ext v
  rw [show pulledForm g p x (inversePulledForm g p x a) v = a v from
    inverse_form_pair _ (pulledForm_positive g p x hp J hJ) a v]
  change a v = g (rawQuadratic p x)
    (fderiv ℝ (rawQuadratic p) x (J.symm _)) (fderiv ℝ (rawQuadratic p) x v)
  rw [hJ]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [inverse_form_pair _ hp]
  simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_PiolaFour
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma adjugate_four_explicit (M : Fin 4 → Fin 4 → ℝ) :
    Matrix.adjugate M = !![(M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 - M 1 2 * M 2 1 * M 3 3 + M 1 2 * M 2 3 * M 3 1 + M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1), -(M 0 1 * M 2 2 * M 3 3 - M 0 1 * M 2 3 * M 3 2 - M 0 2 * M 2 1 * M 3 3 + M 0 2 * M 2 3 * M 3 1 + M 0 3 * M 2 1 * M 3 2 - M 0 3 * M 2 2 * M 3 1), (M 0 1 * M 1 2 * M 3 3 - M 0 1 * M 1 3 * M 3 2 - M 0 2 * M 1 1 * M 3 3 + M 0 2 * M 1 3 * M 3 1 + M 0 3 * M 1 1 * M 3 2 - M 0 3 * M 1 2 * M 3 1), -(M 0 1 * M 1 2 * M 2 3 - M 0 1 * M 1 3 * M 2 2 - M 0 2 * M 1 1 * M 2 3 + M 0 2 * M 1 3 * M 2 1 + M 0 3 * M 1 1 * M 2 2 - M 0 3 * M 1 2 * M 2 1);
      -(M 1 0 * M 2 2 * M 3 3 - M 1 0 * M 2 3 * M 3 2 - M 1 2 * M 2 0 * M 3 3 + M 1 2 * M 2 3 * M 3 0 + M 1 3 * M 2 0 * M 3 2 - M 1 3 * M 2 2 * M 3 0), (M 0 0 * M 2 2 * M 3 3 - M 0 0 * M 2 3 * M 3 2 - M 0 2 * M 2 0 * M 3 3 + M 0 2 * M 2 3 * M 3 0 + M 0 3 * M 2 0 * M 3 2 - M 0 3 * M 2 2 * M 3 0), -(M 0 0 * M 1 2 * M 3 3 - M 0 0 * M 1 3 * M 3 2 - M 0 2 * M 1 0 * M 3 3 + M 0 2 * M 1 3 * M 3 0 + M 0 3 * M 1 0 * M 3 2 - M 0 3 * M 1 2 * M 3 0), (M 0 0 * M 1 2 * M 2 3 - M 0 0 * M 1 3 * M 2 2 - M 0 2 * M 1 0 * M 2 3 + M 0 2 * M 1 3 * M 2 0 + M 0 3 * M 1 0 * M 2 2 - M 0 3 * M 1 2 * M 2 0);
      (M 1 0 * M 2 1 * M 3 3 - M 1 0 * M 2 3 * M 3 1 - M 1 1 * M 2 0 * M 3 3 + M 1 1 * M 2 3 * M 3 0 + M 1 3 * M 2 0 * M 3 1 - M 1 3 * M 2 1 * M 3 0), -(M 0 0 * M 2 1 * M 3 3 - M 0 0 * M 2 3 * M 3 1 - M 0 1 * M 2 0 * M 3 3 + M 0 1 * M 2 3 * M 3 0 + M 0 3 * M 2 0 * M 3 1 - M 0 3 * M 2 1 * M 3 0), (M 0 0 * M 1 1 * M 3 3 - M 0 0 * M 1 3 * M 3 1 - M 0 1 * M 1 0 * M 3 3 + M 0 1 * M 1 3 * M 3 0 + M 0 3 * M 1 0 * M 3 1 - M 0 3 * M 1 1 * M 3 0), -(M 0 0 * M 1 1 * M 2 3 - M 0 0 * M 1 3 * M 2 1 - M 0 1 * M 1 0 * M 2 3 + M 0 1 * M 1 3 * M 2 0 + M 0 3 * M 1 0 * M 2 1 - M 0 3 * M 1 1 * M 2 0);
      -(M 1 0 * M 2 1 * M 3 2 - M 1 0 * M 2 2 * M 3 1 - M 1 1 * M 2 0 * M 3 2 + M 1 1 * M 2 2 * M 3 0 + M 1 2 * M 2 0 * M 3 1 - M 1 2 * M 2 1 * M 3 0), (M 0 0 * M 2 1 * M 3 2 - M 0 0 * M 2 2 * M 3 1 - M 0 1 * M 2 0 * M 3 2 + M 0 1 * M 2 2 * M 3 0 + M 0 2 * M 2 0 * M 3 1 - M 0 2 * M 2 1 * M 3 0), -(M 0 0 * M 1 1 * M 3 2 - M 0 0 * M 1 2 * M 3 1 - M 0 1 * M 1 0 * M 3 2 + M 0 1 * M 1 2 * M 3 0 + M 0 2 * M 1 0 * M 3 1 - M 0 2 * M 1 1 * M 3 0), (M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0)] := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix (n := 3) M i j, Matrix.det_fin_three]
  dsimp only [Matrix.submatrix]
  fin_cases i <;> fin_cases j <;>
    (first | (simp [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]; all_goals first | (norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]; done) | rfl | decide) | (norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]; done) | norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE])

theorem adjugate_divergence_four
    (A : _root_.OAI.Yau.Jets.Coord → Fin 4 → Fin 4 → ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (hA : ∀ i j, DifferentiableAt ℝ (fun z ↦ A z i j) x)
    (hclosed : ∀ a i j, fderiv ℝ (fun z ↦ A z a j) x (Pi.single i 1) =
      fderiv ℝ (fun z ↦ A z a i) x (Pi.single j 1)) (a : Fin 4) :
    ∑ i : Fin 4, fderiv ℝ (fun z ↦ Matrix.adjugate (A z) i a) x (Pi.single i 1) = 0 := by
  simp_rw [adjugate_four_explicit]
  fin_cases a
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ (A z 1 1 * A z 2 2 * A z 3 3 - A z 1 1 * A z 2 3 * A z 3 2 - A z 1 2 * A z 2 1 * A z 3 3 + A z 1 2 * A z 2 3 * A z 3 1 + A z 1 3 * A z 2 1 * A z 3 2 - A z 1 3 * A z 2 2 * A z 3 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ -(A z 1 0 * A z 2 2 * A z 3 3 - A z 1 0 * A z 2 3 * A z 3 2 - A z 1 2 * A z 2 0 * A z 3 3 + A z 1 2 * A z 2 3 * A z 3 0 + A z 1 3 * A z 2 0 * A z 3 2 - A z 1 3 * A z 2 2 * A z 3 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ (A z 1 0 * A z 2 1 * A z 3 3 - A z 1 0 * A z 2 3 * A z 3 1 - A z 1 1 * A z 2 0 * A z 3 3 + A z 1 1 * A z 2 3 * A z 3 0 + A z 1 3 * A z 2 0 * A z 3 1 - A z 1 3 * A z 2 1 * A z 3 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ -(A z 1 0 * A z 2 1 * A z 3 2 - A z 1 0 * A z 2 2 * A z 3 1 - A z 1 1 * A z 2 0 * A z 3 2 + A z 1 1 * A z 2 2 * A z 3 0 + A z 1 2 * A z 2 0 * A z 3 1 - A z 1 2 * A z 2 1 * A z 3 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 1 1 0, hclosed 1 2 0, hclosed 1 2 1, hclosed 1 3 0, hclosed 1 3 1, hclosed 1 3 2, hclosed 2 1 0, hclosed 2 2 0, hclosed 2 2 1, hclosed 2 3 0, hclosed 2 3 1, hclosed 2 3 2, hclosed 3 1 0, hclosed 3 2 0, hclosed 3 2 1, hclosed 3 3 0, hclosed 3 3 1, hclosed 3 3 2]
    ring
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ -(A z 0 1 * A z 2 2 * A z 3 3 - A z 0 1 * A z 2 3 * A z 3 2 - A z 0 2 * A z 2 1 * A z 3 3 + A z 0 2 * A z 2 3 * A z 3 1 + A z 0 3 * A z 2 1 * A z 3 2 - A z 0 3 * A z 2 2 * A z 3 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 2 2 * A z 3 3 - A z 0 0 * A z 2 3 * A z 3 2 - A z 0 2 * A z 2 0 * A z 3 3 + A z 0 2 * A z 2 3 * A z 3 0 + A z 0 3 * A z 2 0 * A z 3 2 - A z 0 3 * A z 2 2 * A z 3 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 2 1 * A z 3 3 - A z 0 0 * A z 2 3 * A z 3 1 - A z 0 1 * A z 2 0 * A z 3 3 + A z 0 1 * A z 2 3 * A z 3 0 + A z 0 3 * A z 2 0 * A z 3 1 - A z 0 3 * A z 2 1 * A z 3 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 2 1 * A z 3 2 - A z 0 0 * A z 2 2 * A z 3 1 - A z 0 1 * A z 2 0 * A z 3 2 + A z 0 1 * A z 2 2 * A z 3 0 + A z 0 2 * A z 2 0 * A z 3 1 - A z 0 2 * A z 2 1 * A z 3 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 0 1 0, hclosed 0 2 0, hclosed 0 2 1, hclosed 0 3 0, hclosed 0 3 1, hclosed 0 3 2, hclosed 2 1 0, hclosed 2 2 0, hclosed 2 2 1, hclosed 2 3 0, hclosed 2 3 1, hclosed 2 3 2, hclosed 3 1 0, hclosed 3 2 0, hclosed 3 2 1, hclosed 3 3 0, hclosed 3 3 1, hclosed 3 3 2]
    ring
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ (A z 0 1 * A z 1 2 * A z 3 3 - A z 0 1 * A z 1 3 * A z 3 2 - A z 0 2 * A z 1 1 * A z 3 3 + A z 0 2 * A z 1 3 * A z 3 1 + A z 0 3 * A z 1 1 * A z 3 2 - A z 0 3 * A z 1 2 * A z 3 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 1 2 * A z 3 3 - A z 0 0 * A z 1 3 * A z 3 2 - A z 0 2 * A z 1 0 * A z 3 3 + A z 0 2 * A z 1 3 * A z 3 0 + A z 0 3 * A z 1 0 * A z 3 2 - A z 0 3 * A z 1 2 * A z 3 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 1 1 * A z 3 3 - A z 0 0 * A z 1 3 * A z 3 1 - A z 0 1 * A z 1 0 * A z 3 3 + A z 0 1 * A z 1 3 * A z 3 0 + A z 0 3 * A z 1 0 * A z 3 1 - A z 0 3 * A z 1 1 * A z 3 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 1 1 * A z 3 2 - A z 0 0 * A z 1 2 * A z 3 1 - A z 0 1 * A z 1 0 * A z 3 2 + A z 0 1 * A z 1 2 * A z 3 0 + A z 0 2 * A z 1 0 * A z 3 1 - A z 0 2 * A z 1 1 * A z 3 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 0 1 0, hclosed 0 2 0, hclosed 0 2 1, hclosed 0 3 0, hclosed 0 3 1, hclosed 0 3 2, hclosed 1 1 0, hclosed 1 2 0, hclosed 1 2 1, hclosed 1 3 0, hclosed 1 3 1, hclosed 1 3 2, hclosed 3 1 0, hclosed 3 2 0, hclosed 3 2 1, hclosed 3 3 0, hclosed 3 3 1, hclosed 3 3 2]
    ring
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ -(A z 0 1 * A z 1 2 * A z 2 3 - A z 0 1 * A z 1 3 * A z 2 2 - A z 0 2 * A z 1 1 * A z 2 3 + A z 0 2 * A z 1 3 * A z 2 1 + A z 0 3 * A z 1 1 * A z 2 2 - A z 0 3 * A z 1 2 * A z 2 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 1 2 * A z 2 3 - A z 0 0 * A z 1 3 * A z 2 2 - A z 0 2 * A z 1 0 * A z 2 3 + A z 0 2 * A z 1 3 * A z 2 0 + A z 0 3 * A z 1 0 * A z 2 2 - A z 0 3 * A z 1 2 * A z 2 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 1 1 * A z 2 3 - A z 0 0 * A z 1 3 * A z 2 1 - A z 0 1 * A z 1 0 * A z 2 3 + A z 0 1 * A z 1 3 * A z 2 0 + A z 0 3 * A z 1 0 * A z 2 1 - A z 0 3 * A z 1 1 * A z 2 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 1 1 * A z 2 2 - A z 0 0 * A z 1 2 * A z 2 1 - A z 0 1 * A z 1 0 * A z 2 2 + A z 0 1 * A z 1 2 * A z 2 0 + A z 0 2 * A z 1 0 * A z 2 1 - A z 0 2 * A z 1 1 * A z 2 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 0 1 0, hclosed 0 2 0, hclosed 0 2 1, hclosed 0 3 0, hclosed 0 3 1, hclosed 0 3 2, hclosed 1 1 0, hclosed 1 2 0, hclosed 1 2 1, hclosed 1 3 0, hclosed 1 3 1, hclosed 1 3 2, hclosed 2 1 0, hclosed 2 2 0, hclosed 2 2 1, hclosed 2 3 0, hclosed 2 3 1, hclosed 2 3 2]
    ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_JacobianCalculus
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma jacobian_smooth (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ jacobian F x i j) :=
  (ContinuousLinearMap.proj i : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).contDiff.comp
    ((hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

lemma jacobian_closed (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (x : _root_.OAI.Yau.Jets.Coord) (a i j : Fin 4) :
    fderiv ℝ (fun z ↦ jacobian F z a j) x (Pi.single i 1) =
      fderiv ℝ (fun z ↦ jacobian F z a i) x (Pi.single j 1) := by
  have hd := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have he (k : Fin 4) : fderiv ℝ (fun z ↦ jacobian F z a k) x =
      (ContinuousLinearMap.proj a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).comp
        ((fderiv ℝ (fun z ↦ fderiv ℝ F z) x).flip (Pi.single k 1)) := by
    change fderiv ℝ ((ContinuousLinearMap.proj a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) ∘
      (fun z ↦ fderiv ℝ F z (Pi.single k 1))) x = _
    rw [fderiv_comp x (ContinuousLinearMap.proj a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).differentiableAt
      (hd.clm_apply (differentiableAt_const _)), ContinuousLinearMap.fderiv]
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [he,he]
  exact congrArg (fun v : _root_.OAI.Yau.Jets.Coord ↦ v a)
    (hF.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (Pi.single i 1) (Pi.single j 1))

lemma clm_coord_sum (L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ) (v : _root_.OAI.Yau.Jets.Coord) :
    L v = ∑ j : Fin 4, (v j : ℂ) * L (Pi.single j 1) := by
  have hv : v = ∑ j : Fin 4, v j • Pi.single j (1:ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, Complex.real_smul]

lemma coordPartial_comp (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hF : DifferentiableAt ℝ F x) (u : _root_.OAI.Yau.Jets.Coord → ℂ)
    (hu : DifferentiableAt ℝ u (F x)) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (u ∘ F) x =
      ∑ j : Fin 4, (jacobian F x j i : ℂ) * _root_.OAI.Yau.Jets.coordPartial j u (F x) := by
  unfold _root_.OAI.Yau.Jets.coordPartial
  rw [fderiv_comp x hu hF]
  exact clm_coord_sum (fderiv ℝ u (F x)) (fderiv ℝ F x (Pi.single i 1))

lemma coordPartial_sum_at (f : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ ∑ j, f j z) x = ∑ j, _root_.OAI.Yau.Jets.coordPartial i (f j) x := by
  unfold _root_.OAI.Yau.Jets.coordPartial
  rw [fderiv_fun_sum (fun j _ ↦ hf j)]
  simp

lemma adjugate_entry_smooth (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun z ↦ (jacobian F z).adjugate i j) := by
  simp only [Matrix.adjugate_fin_succ_eq_det_submatrix, Matrix.det_fin_three,
    Matrix.submatrix_apply]
  have hJ := jacobian_smooth F hF
  fun_prop

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_PiolaFlux
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma adjugate_divergence_complex (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (x : _root_.OAI.Yau.Jets.Coord) (a : Fin 4) :
    ∑ i, _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) x = 0 := by
  simp_rw [coordPartial_ofReal_at _ x
    ((adjugate_entry_smooth F hF _ _).differentiable (by simp) x)]
  rw [← Complex.ofReal_sum, adjugate_divergence_four (jacobian F) x
    (fun i j ↦ (jacobian_smooth F hF i j).differentiable (by simp) x)
    (jacobian_closed F hF x)]
  rfl

lemma jacobian_mul_adjugate_complex (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) (a b : Fin 4) :
    ∑ i, ((jacobian F x).adjugate i a : ℂ) * (jacobian F x b i : ℂ) =
      if b=a then ((jacobian F x).det : ℂ) else 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ ↦ M b a)
    (Matrix.mul_adjugate (jacobian F x))
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  have hh := congrArg Complex.ofReal h
  push_cast at hh
  split_ifs with hba <;> simp [hba,mul_comm] at hh ⊢ <;> exact hh

theorem signedPiola_divergence (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hV : ∀ a, DifferentiableAt ℝ (V a) (F x)) :
    complexDivergence (signedPiola F V) x =
      ((jacobian F x).det : ℂ) * complexDivergence V (F x) := by
  have hFc (i a : Fin 4) : DifferentiableAt ℝ
      (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((adjugate_entry_smooth F hF i a).differentiable (by simp) x)
  have hVc (a : Fin 4) : DifferentiableAt ℝ (V a ∘ F) x :=
    (hV a).comp x (hF.differentiable (by simp) x)
  have hsum (i : Fin 4) : _root_.OAI.Yau.Jets.coordPartial i (signedPiola F V i) x =
      ∑ a, _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ ((jacobian F z).adjugate i a : ℂ) * V a (F z)) x :=
    coordPartial_sum_at _ x (fun a ↦ (hFc i a).mul (hVc a)) i
  have hprod (i a : Fin 4) := coordPartial_mul_at
    (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) (fun z ↦ V a (F z)) x (hFc i a) (hVc a) i
  unfold complexDivergence
  simp_rw [hsum,hprod]
  simp only [Finset.sum_add_distrib]
  have hz : (∑ i, ∑ a, _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) x *
      V a (F x)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, adjugate_divergence_complex F hF x]
    simp
  rw [hz, zero_add]
  have hc (a i : Fin 4) := coordPartial_comp F x
    (hF.differentiable (by simp) x) (V a) (hV a) i
  simp only [Function.comp_def] at hc
  simp_rw [hc]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans _ (by rfl)
  calc
    _ = ∑ a, ∑ b, (∑ i, ((jacobian F x).adjugate i a : ℂ) *
        (jacobian F x b i : ℂ)) * _root_.OAI.Yau.Jets.coordPartial b (V a) (F x) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by
      simp_rw [jacobian_mul_adjugate_complex]
      simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AbsolutePiola
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section

lemma local_absolute_ratio (d : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (hd : ContinuousAt d x) (hn : d x ≠ 0) :
    ∃ s : ℝ, s * d x = |d x| ∧ ∀ᶠ z in 𝓝 x, |d z| / d z = s := by
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine ⟨-1, by simp [abs_of_neg hneg], ?_⟩
    filter_upwards [hd.eventually (gt_mem_nhds hneg)] with z hz
    simp [abs_of_neg hz, ne_of_lt hz]
  · refine ⟨1, by simp [abs_of_pos hpos], ?_⟩
    filter_upwards [hd.eventually (lt_mem_nhds hpos)] with z hz
    simp [abs_of_pos hz, ne_of_gt hz]

lemma signedPiola_differentiableAt (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hV : ∀ a, DifferentiableAt ℝ (V a) (F x)) (i : Fin 4) :
    DifferentiableAt ℝ (signedPiola F V i) x := by
  apply DifferentiableAt.fun_sum
  intro a _
  exact (Complex.ofRealCLM.differentiableAt.comp x
    ((adjugate_entry_smooth F hF i a).differentiable (by simp) x)).mul
      ((hV a).comp x (hF.differentiable (by simp) x))

theorem absolutePiola_divergence (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (hF : ContDiff ℝ ∞ F)
    (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hV : ∀ a, DifferentiableAt ℝ (V a) (F x))
    (hdet : (jacobian F x).det ≠ 0) :
    complexDivergence (absolutePiola F V) x =
      ((|(jacobian F x).det| : ℝ) : ℂ) * complexDivergence V (F x) := by
  have hd : ContinuousAt (fun z ↦ (jacobian F z).det) x :=
    (coordDet_smooth.continuous.comp (hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous).continuousAt
  obtain ⟨s,hs,hr⟩ := local_absolute_ratio _ x hd hdet
  have he (i : Fin 4) : absolutePiola F V i =ᶠ[𝓝 x]
      fun z ↦ (s:ℂ) * signedPiola F V i z := by
    filter_upwards [hr] with z hz
    simp only [absolutePiola,hz]
  have hpartial (i : Fin 4) : _root_.OAI.Yau.Jets.coordPartial i (absolutePiola F V i) x =
      (s:ℂ) * _root_.OAI.Yau.Jets.coordPartial i (signedPiola F V i) x := by
    unfold _root_.OAI.Yau.Jets.coordPartial
    rw [(he i).fderiv_eq]
    rw [fderiv_const_mul (signedPiola_differentiableAt F hF V x hV i)]
    simp
  unfold complexDivergence
  simp_rw [hpartial]
  rw [← Finset.mul_sum]
  change (s:ℂ) * complexDivergence (signedPiola F V) x = _
  rw [signedPiola_divergence F hF V x hV, ← mul_assoc, ← Complex.ofReal_mul, hs]
  rfl

end
end Yau.Geometry

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

lemma chartPushforward_pullback (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ F.source) :
    chartPushforward F u (F x) = u x := by
  simp [chartPushforward,F.map_source hx,F.left_inv hx]

lemma chartPushforward_support (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : HasCompactSupport u) (hs : tsupport u ⊆ F.source) :
    tsupport (chartPushforward F u) ⊆ F '' tsupport u := by
  have hc : IsCompact (F '' tsupport u) := hu.image_of_continuousOn (F.continuousOn.mono hs)
  apply closure_minimal _ hc.isClosed
  intro z hz
  by_cases ht : z ∈ F.target
  · refine ⟨F.symm z, ?_, F.right_inv ht⟩
    apply subset_closure
    intro he
    exact hz (by simp [chartPushforward,ht,he])
  · exact False.elim (hz (by simp [chartPushforward,ht]))

theorem chartPushforward_smooth (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (hF : ContDiffOn ℝ ∞ F.symm F.target)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ F.source) :
    ContDiff ℝ ∞ (chartPushforward F u) ∧ HasCompactSupport (chartPushforward F u) ∧
      tsupport (chartPushforward F u) ⊆ F '' tsupport u := by
  have hsupport := chartPushforward_support F u hc hs
  have hcompact : IsCompact (F '' tsupport u) := hc.image_of_continuousOn (F.continuousOn.mono hs)
  refine ⟨?_,hcompact.of_isClosed_subset isClosed_closure hsupport,hsupport⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ F.target
  · exact (hu.contDiffAt.comp z (hF.contDiffAt (F.open_target.mem_nhds hz))).congr_of_eventuallyEq
      (chartPushforward_eventually F u z hz)
  · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro h
    obtain ⟨x,hx,rfl⟩ := hsupport h
    exact hz (F.map_source (hs hx))

theorem chartPushforward_derivative (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (z : _root_.OAI.Yau.Jets.Coord) (hz : z ∈ F.target) (k : ℕ) :
    iteratedFDeriv ℝ k (chartPushforward F u) z = iteratedFDeriv ℝ k (u ∘ F.symm) z :=
  ((chartPushforward_eventually F u z hz).iteratedFDeriv ℝ k).self_of_nhds

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

theorem chart_wave_size_transfer (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (hF : ContDiffOn ℝ ∞ F.symm F.target) (u : _root_.OAI.Yau.Jets.Coord → ℂ)
    (hu : ContDiff ℝ ∞ u) (z : _root_.OAI.Yau.Jets.Coord) (hz : z ∈ F.target)
    (k : ℕ) (C D E N : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hN : 1 ≤ N)
    (hsize : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i u (F.symm z)‖ ≤ C*N^i*E)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i (F.symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) z‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ k (chartPushforward F u) z‖ ≤ (k.factorial*C*D^k)*N^k*E := by
  rw [chartPushforward_derivative F u z hz k]
  have h := chart_comp_derivative_bound F hF u hu.contDiffOn z hz k (C*N^k*E) D
    (fun i hi ↦ (hsize i hi).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN hi) hC) hE)) hD
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem chart_residual_bound_transfer (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (hF : ContDiffOn ℝ ∞ F.symm F.target) (R : _root_.OAI.Yau.Jets.Coord → ℂ)
    (hR : ContDiffOn ℝ ∞ R F.source) (z : _root_.OAI.Yau.Jets.Coord) (hz : z ∈ F.target)
    (k : ℕ) (C D E N K : ℝ)
    (hres : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i R (F.symm z)‖ ≤ C*N^(-K)*E)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i (F.symm : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) z‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ k (R ∘ F.symm) z‖ ≤ (k.factorial*C*D^k)*N^(-K)*E := by
  have h := chart_comp_derivative_bound F hF R hR z hz k (C*N^(-K)*E) D hres hD
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricFluxPullback
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

lemma covector_basis (a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) :
    a = ∑ j : Fin 4, a (Pi.single j 1) • (ContinuousLinearMap.proj j : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) := by
  ext v
  have hv : v = ∑ j : Fin 4, v j • Pi.single j (1:ℝ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, mul_comm]

lemma inversePulledForm_covector
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (a : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) :
    inversePulledForm g p x (a.comp J.toContinuousLinearMap) =
      J.symm (ContinuousLinearMap.inverse (g (rawQuadratic p x)) a) := by
  rw [inversePulledForm_transform g p x hp J hJ]
  congr 2
  ext v
  simp

lemma principal_jacobian_sum
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i a : Fin 4) :
    ∑ j, chartPrincipal g i j p x * jacobian (rawQuadratic p) x a j =
      (J.symm (ContinuousLinearMap.inverse (g (rawQuadratic p x)) (ContinuousLinearMap.proj a))) i := by
  have h := congrArg (fun v : _root_.OAI.Yau.Jets.Coord ↦ v i)
    (inversePulledForm_covector g p x hp J hJ (ContinuousLinearMap.proj a))
  conv_lhs at h => rw [covector_basis ((ContinuousLinearMap.proj a).comp J.toContinuousLinearMap)]
  simpa [chartPrincipal,jacobian,hJ,map_sum,map_smul,mul_comm] using h

lemma adjugate_equiv_apply (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (v : _root_.OAI.Yau.Jets.Coord) (i : Fin 4) :
    ∑ a, (LinearMap.toMatrix' J.toLinearMap).adjugate i a * v a =
      coordDet J.toContinuousLinearMap * J.symm v i := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ ↦ Matrix.mulVec M (J.symm v) i)
    (Matrix.adjugate_mul (LinearMap.toMatrix' J.toLinearMap))
  rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec] at h
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h
  change (LinearMap.toMatrix' J.toLinearMap).adjugate.mulVec (J (J.symm v)) i =
    coordDet J.toContinuousLinearMap * J.symm v i at h
  rw [J.apply_symm_apply] at h
  exact h

theorem determinant_principal_jacobian
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i a : Fin 4) :
    (jacobian (rawQuadratic p) x).det *
      (∑ j, chartPrincipal g i j p x * jacobian (rawQuadratic p) x a j) =
      ∑ b, (jacobian (rawQuadratic p) x).adjugate i b *
        sourcePrincipal g b a (rawQuadratic p x) := by
  rw [principal_jacobian_sum g p x hp J hJ]
  have hj : jacobian (rawQuadratic p) x = LinearMap.toMatrix' J.toLinearMap := by
    ext b j
    simp [jacobian,hJ,LinearMap.toMatrix'_apply]
  rw [hj]
  exact (adjugate_equiv_apply J
    (ContinuousLinearMap.inverse (g (rawQuadratic p x)) (ContinuousLinearMap.proj a)) i).symm

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ComplexMetricFlux
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourcePrincipal_smooth_at
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (sourcePrincipal g i j) x := by
  have hi : ContDiffAt ℝ ∞ (fun z ↦ ContinuousLinearMap.inverse (g z)) x := by
    have h := contDiffAt_map_inverse (n := ∞) (positiveMetricEquiv (g x) hp)
    exact h.comp x hg.contDiffAt
  exact (ContinuousLinearMap.proj i : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ).contDiff.contDiffAt.comp x
    (hi.clm_apply contDiffAt_const)

lemma sourceFlux_smooth_at
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u)
    (x : _root_.OAI.Yau.Jets.Coord) (hp : ∀ v, v ≠ 0 → 0 < g x v v) (i : Fin 4) :
    ContDiffAt ℝ ∞ (sourceFlux g w u i) x := by
  apply ContDiffAt.sum
  intro j _
  exact ((Complex.ofRealCLM.contDiff.comp hw).contDiffAt.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp x (sourcePrincipal_smooth_at g hg x hp i j))).mul
      (coordPartial_contDiff hu j).contDiffAt

lemma complex_principal_jacobian
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (i a : Fin 4) :
    ((jacobian (rawQuadratic p) x).det : ℂ) *
      (∑ j, complexPrincipal g i j p x * (jacobian (rawQuadratic p) x a j : ℂ)) =
      ∑ b, ((jacobian (rawQuadratic p) x).adjugate i b : ℂ) *
        (sourcePrincipal g b a (rawQuadratic p x) : ℂ) := by
  unfold complexPrincipal
  exact_mod_cast determinant_principal_jacobian g p x hp J hJ i a

lemma complex_gradient_flux_transform
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : DifferentiableAt ℝ u (rawQuadratic p x)) (i : Fin 4) :
    ((jacobian (rawQuadratic p) x).det : ℂ) *
      (∑ j, complexPrincipal g i j p x * _root_.OAI.Yau.Jets.coordPartial j (u ∘ rawQuadratic p) x) =
      ∑ b, ((jacobian (rawQuadratic p) x).adjugate i b : ℂ) *
        (∑ a, (sourcePrincipal g b a (rawQuadratic p x) : ℂ) * _root_.OAI.Yau.Jets.coordPartial a u (rawQuadratic p x)) := by
  have hF : DifferentiableAt ℝ (rawQuadratic p) x :=
    (rawQuadratic_smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  simp_rw [coordPartial_comp (rawQuadratic p) x hF u hu]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, (((jacobian (rawQuadratic p) x).det : ℂ) *
        ∑ j, complexPrincipal g i j p x * (jacobian (rawQuadratic p) x a j : ℂ)) *
          _root_.OAI.Yau.Jets.coordPartial a u (rawQuadratic p x) := by
      simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ = _ := by
      simp_rw [complex_principal_jacobian g p x hp J hJ]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]

theorem actual_pulled_flux
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g (rawQuadratic p x) v v)
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : DifferentiableAt ℝ u (rawQuadratic p x)) (i : Fin 4) :
    pulledFlux g w p (u ∘ rawQuadratic p) i x =
      absolutePiola (rawQuadratic p) (sourceFlux g w u) i x := by
  have he := complex_gradient_flux_transform g p x hp J hJ u hu i
  have hd : (jacobian (rawQuadratic p) x).det ≠ 0 := by
    change coordDet (fderiv ℝ (rawQuadratic p) x) ≠ 0
    rw [hJ]
    exact coordDet_equiv_ne_zero J
  have hdC := Complex.ofReal_ne_zero.mpr hd
  have hsource : signedPiola (rawQuadratic p) (sourceFlux g w u) i x =
      (w (rawQuadratic p x) : ℂ) *
        (∑ b, ((jacobian (rawQuadratic p) x).adjugate i b : ℂ) *
          ∑ a, (sourcePrincipal g b a (rawQuadratic p x) : ℂ) * _root_.OAI.Yau.Jets.coordPartial a u (rawQuadratic p x)) := by
    simp only [signedPiola,sourceFlux,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold absolutePiola
  rw [hsource, ← he]
  have hpull : pulledFlux g w p (u ∘ rawQuadratic p) i x =
      (w (rawQuadratic p x) : ℂ) * ((|(jacobian (rawQuadratic p) x).det| : ℝ) : ℂ) *
        ∑ j, complexPrincipal g i j p x * _root_.OAI.Yau.Jets.coordPartial j (u ∘ rawQuadratic p) x := by
    simp only [pulledFlux,chartDensity,coordDet,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]
    rfl
  rw [hpull]
  push_cast
  field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedDivergenceInvariance
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma weightedCoordinateOperator_divergence (W : _root_.OAI.Yau.Jets.Coord → ℂ)
    (a : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (u : _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord)
    (hflux : ∀ i j, DifferentiableAt ℝ (fun z ↦ W z * a i j z) x)
    (hu : ∀ j, DifferentiableAt ℝ (_root_.OAI.Yau.Jets.coordPartial j u) x) :
    weightedCoordinateOperator W a u x = (W x)⁻¹ *
      complexDivergence (fun i z ↦ ∑ j, (W z * a i j z) * _root_.OAI.Yau.Jets.coordPartial j u z) x := by
  unfold weightedCoordinateOperator complexDivergence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (coordPartial_sum_at _ x (fun j ↦ (hflux i j).mul (hu j)) i).symm

theorem actual_weighted_coordinate_invariance
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord)
    (hwpos : 0 < w (rawQuadratic p x))
    (J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (hJ : fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) :
    smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
      (fun j ↦ complexDrift g w j p) (u ∘ rawQuadratic p) x =
        sourceWeightedOperator g w u (rawQuadratic p x) := by
  have hF : ContDiff ℝ ∞ (rawQuadratic p) :=
    rawQuadratic_smooth.comp (contDiff_const.prodMk contDiff_id)
  have huc := hu.comp hF
  have hJe : ∀ᶠ z in 𝓝 x, ∃ Jz : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      Jz.toContinuousLinearMap = fderiv ℝ (rawQuadratic p) z :=
    (hF.fderiv_right (m := ∞) (by simp)).continuous.continuousAt.eventually
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨J,hJ.symm⟩)
  have he (i : Fin 4) : pulledFlux g w p (u ∘ rawQuadratic p) i =ᶠ[𝓝 x]
      absolutePiola (rawQuadratic p) (sourceFlux g w u) i := by
    filter_upwards [hJe] with z hz
    obtain ⟨Jz,hJz⟩ := hz
    exact actual_pulled_flux g w p z (hp _) Jz hJz.symm u
      (hu.differentiable (by simp) _) i
  have hdiv : complexDivergence (pulledFlux g w p (u ∘ rawQuadratic p)) x =
      complexDivergence (absolutePiola (rawQuadratic p) (sourceFlux g w u)) x := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ ↦ L (Pi.single i 1)) (he i).fderiv_eq
  have hflux (i j : Fin 4) : DifferentiableAt ℝ
      (fun z ↦ (chartDensity w p z : ℂ) * complexPrincipal g i j p z) x := by
    have hW := ((chartDensity_smooth_at w hw p x J hJ).comp x
      (contDiffAt_const.prodMk contDiffAt_id))
    have ha := ((chartPrincipal_smooth_at g hg p x (hp _) J hJ i j).comp x
      (contDiffAt_const.prodMk contDiffAt_id))
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hW).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x ha)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [← actual_chart_weighted_operator g hg w hw p x (hp _) hwpos J hJ
    (u ∘ rawQuadratic p) huc]
  rw [weightedCoordinateOperator_divergence _ _ _ x hflux
    (fun j ↦ (coordPartial_contDiff huc j).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
  change (chartDensity w p x : ℂ)⁻¹ *
    complexDivergence (pulledFlux g w p (u ∘ rawQuadratic p)) x = _
  rw [hdiv, absolutePiola_divergence (rawQuadratic p) hF (sourceFlux g w u) x
    (fun a ↦ (sourceFlux_smooth_at g hg w hw u hu _ (hp _) a).differentiableAt (by simp))
    (by change coordDet (fderiv ℝ (rawQuadratic p) x) ≠ 0
        rw [hJ]; exact coordDet_equiv_ne_zero J)]
  have hd : (|(jacobian (rawQuadratic p) x).det| : ℝ) ≠ 0 := by
    apply abs_ne_zero.mpr
    change coordDet (fderiv ℝ (rawQuadratic p) x) ≠ 0
    rw [hJ]; exact coordDet_equiv_ne_zero J
  unfold sourceWeightedOperator chartDensity
  change ((w (rawQuadratic p x) * |(jacobian (rawQuadratic p) x).det| : ℝ) : ℂ)⁻¹ * _ = _
  have hdC := Complex.ofReal_ne_zero.mpr hd
  have hwC := Complex.ofReal_ne_zero.mpr (ne_of_gt hwpos)
  push_cast
  field_simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CommonInvariantCharts
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

theorem compact_invariant_charts {s : Set T} (hs : IsCompact s)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord) (hB : Continuous B)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hyU : ∀ t ∈ s, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x) :
    ∃ r > 0, ∃ d > 0, ∀ t ∈ s, ∃ F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord,
      (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = rawQuadratic (y t,(e t).toContinuousLinearMap,B t) ∧
      F.source = ball 0 r ∧ closedBall (y t) d ⊆ F.target ∧ F.target ⊆ U ∧
      ContDiffOn ℝ ∞ F.symm F.target ∧
      (∀ x ∈ F.source, ∃ J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
        fderiv ℝ (rawQuadratic (y t,(e t).toContinuousLinearMap,B t)) x = J.toContinuousLinearMap) ∧
      ∀ (u : _root_.OAI.Yau.Jets.Coord → ℂ), ContDiff ℝ ∞ u → ∀ x ∈ F.source,
        smoothSecondOrder (fun i j ↦ complexPrincipal g i j (y t,(e t).toContinuousLinearMap,B t))
          (fun j ↦ complexDrift g w j (y t,(e t).toContinuousLinearMap,B t)) (u ∘ F) x =
          sourceWeightedOperator g w u (F x) := by
  obtain ⟨R,hR,hRi⟩ := compact_quadratic_chart_domain hs y hy e he B hB hU hyU
  have hD : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ fderiv ℝ
      (quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  obtain ⟨r,hr,hrR,d,hd,hF⟩ := compact_common_chart hs
    (fun t ↦ quadraticChartMap (y t) (e t) (B t))
    (fun t ↦ quadraticChartMap_smooth _ _ _) hD e he
    (fun t ↦ (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv) R hR
  refine ⟨r,hr,d,hd,?_⟩
  intro t ht
  obtain ⟨F,hFe,hFs,hFt⟩ := hF t ht
  have hFR (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ F.source) : ‖x‖ < R := by
    rw [hFs,mem_ball,dist_zero_right] at hx
    exact hx.trans_le hrR
  have hsource (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ F.source) : F x ∈ U := by
    rw [hFe]
    exact (hRi t ht x (hFR x hx)).1
  have hJac (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ F.source) := (hRi t ht x (hFR x hx)).2
  have hsm : ContDiff ℝ ∞ (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) := by
    rw [hFe]; exact quadraticChartMap_smooth _ _ _
  refine ⟨F,hFe,hFs,by simpa only [quadraticChartMap_zero] using hFt,?_,?_,?_,?_⟩
  · intro z hz
    simpa only [F.right_inv hz] using hsource (F.symm z) (F.map_target hz)
  · intro z hz
    obtain ⟨J,hJe⟩ := hJac (F.symm z) (F.map_target hz)
    have hder : HasFDerivAt (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) J.toContinuousLinearMap (F.symm z) := by
      rw [hFe,hJe]
      exact (quadraticChartMap_smooth _ _ _).differentiable (by simp) _ |>.hasFDerivAt
    exact (F.contDiffAt_symm hz hder hsm.contDiffAt).contDiffWithinAt
  · intro x hx
    obtain ⟨J,hJe⟩ := hJac x hx
    exact ⟨J,hJe.symm⟩
  · intro u hu x hx
    obtain ⟨J,hJe⟩ := hJac x hx
    rw [hFe]
    have hwx : 0 < w (rawQuadratic (y t,(e t).toContinuousLinearMap,B t) x) := by
      change 0 < w (quadraticChartMap (y t) (e t) (B t) x)
      rw [← hFe]
      exact hwpos (F x) (hsource x hx)
    exact actual_weighted_coordinate_invariance g hg hp w hw
      (y t,(e t).toContinuousLinearMap,B t) x hwx J hJe.symm u hu

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartNormComparison
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff NNReal
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem compact_chart_norm_bound {s : Set T} (hs : IsCompact s)
    (p : T → QuadParam _root_.OAI.Yau.Jets.Coord) (hp : Continuous p) (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ t ∈ s, ∀ x ∈ closedBall (0:_root_.OAI.Yau.Jets.Coord) R,
      ‖rawQuadratic (p t) x - (p t).1‖ ≤ L*‖x‖ := by
  have hc : Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ fderiv ℝ (rawQuadratic (p z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      ((hp.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨C,hC⟩ := (hs.prod (isCompact_closedBall (0:_root_.OAI.Yau.Jets.Coord) R)).exists_bound_of_continuousOn hc.continuousOn
  let L : ℝ≥0 := ⟨max C 1, by positivity⟩
  refine ⟨L,le_max_right _ _,?_⟩
  intro t ht x hx
  have hsm : ContDiff ℝ ∞ (rawQuadratic (p t)) :=
    rawQuadratic_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hl : LipschitzOnWith L (rawQuadratic (p t)) (closedBall 0 R) := by
    apply (convex_closedBall (0:_root_.OAI.Yau.Jets.Coord) R).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro z _
      exact hsm.differentiable (by simp) z
    · intro z hz
      exact (hC (t,z) ⟨ht,hz⟩).trans (le_max_left _ _)
  have h := hl.dist_le_mul x hx 0 (by simpa using hR)
  simpa [rawQuadratic,dist_eq_norm] using h

lemma gaussian_chart_norm_bound (c N L a b : ℝ)
    (hc : 0 ≤ c) (hN : 0 ≤ N) (hL : 0 < L) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b ≤ L*a) : (c/L^2)*N*b^2 ≤ c*N*a^2 := by
  have hsq : b^2 ≤ L^2*a^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hb (mul_nonneg hL.le ha)).mpr hab
  have hh : b^2/L^2 ≤ a^2 := (div_le_iff₀ (sq_pos_of_pos hL)).mpr (by nlinarith)
  have he := mul_le_mul_of_nonneg_left hh (mul_nonneg hc hN)
  calc
    (c/L^2)*N*b^2 = (c*N)*(b^2/L^2) := by ring
    _ ≤ c*N*a^2 := he

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransportedOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section

lemma smoothSecondOrder_congr_germ (a : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (b : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) {f u : _root_.OAI.Yau.Jets.Coord → ℂ} {x : _root_.OAI.Yau.Jets.Coord} (he : f =ᶠ[𝓝 x] u) :
    smoothSecondOrder a b f x = smoothSecondOrder a b u x := by
  have hfirst (i : Fin 4) := (coordPartial_eventuallyEq he i).self_of_nhds
  have hsecond (i j : Fin 4) := (coordPartial_eventuallyEq (coordPartial_eventuallyEq he j) i).self_of_nhds
  simp only [smoothSecondOrder,hfirst,hsecond]

theorem transported_operator_identity
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (hF : (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = rawQuadratic p)
    (hInv : ContDiffOn ℝ ∞ F.symm F.target)
    (hJ : ∀ x ∈ F.source, ∃ J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (hwp : ∀ z ∈ F.target, 0 < w z)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ F.source)
    (z : _root_.OAI.Yau.Jets.Coord) (hz : z ∈ F.target) :
    sourceWeightedOperator g w (chartPushforward F u) z =
      smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
        (fun j ↦ complexDrift g w j p) u (F.symm z) := by
  have hx := F.map_target hz
  obtain ⟨J,hJe⟩ := hJ (F.symm z) hx
  have he : (chartPushforward F u) ∘ rawQuadratic p =ᶠ[𝓝 (F.symm z)] u := by
    filter_upwards [F.open_source.mem_nhds hx] with x hx'
    rw [← hF]
    exact chartPushforward_pullback F u x hx'
  have h := actual_weighted_coordinate_invariance g hg hp w hw p (F.symm z)
    (by rw [← hF,F.right_inv hz]; exact hwp z hz) J hJe
    (chartPushforward F u) (chartPushforward_smooth F hInv u hu hc hs).1
  rw [smoothSecondOrder_congr_germ _ _ he] at h
  rw [← hF,F.right_inv hz] at h
  exact h.symm

theorem transported_residual_derivative
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (hF : (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = rawQuadratic p)
    (hInv : ContDiffOn ℝ ∞ F.symm F.target)
    (hJ : ∀ x ∈ F.source, ∃ J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (hwp : ∀ z ∈ F.target, 0 < w z)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ F.source)
    (lam : ℂ) (z : _root_.OAI.Yau.Jets.Coord) (hz : z ∈ F.target) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w (chartPushforward F u) z +
      lam * chartPushforward F u z) z =
    iteratedFDeriv ℝ k ((fun x ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
      (fun j ↦ complexDrift g w j p) u x + lam*u x) ∘ F.symm) z := by
  have he : (fun z ↦ sourceWeightedOperator g w (chartPushforward F u) z + lam * chartPushforward F u z) =ᶠ[𝓝 z]
      (fun x ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
        (fun j ↦ complexDrift g w j p) u x + lam*u x) ∘ F.symm := by
    filter_upwards [F.open_target.mem_nhds hz] with z hz'
    rw [transported_operator_identity g hg hp w hw p F hF hInv hJ hwp u hu hc hs z hz']
    simp [chartPushforward,hz']
  exact (he.iteratedFDeriv ℝ k).self_of_nhds

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_LocalCoordinateResidual
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

lemma actual_coordinate_residual_smoothOn
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : QuadParam _root_.OAI.Yau.Jets.Coord) (U : Set _root_.OAI.Yau.Jets.Coord)
    (hJ : ∀ x ∈ U, ∃ J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      fderiv ℝ (rawQuadratic p) x = J.toContinuousLinearMap)
    (hwp : ∀ x ∈ U, 0 < w (rawQuadratic p x))
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (lam : ℂ) :
    ContDiffOn ℝ ∞ (fun x ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j p)
      (fun j ↦ complexDrift g w j p) u x + lam*u x) U := by
  have hG (i j : Fin 4) : ContDiffOn ℝ ∞ (complexPrincipal g i j p) U := by
    intro x hx
    obtain ⟨J,hJe⟩ := hJ x hx
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((chartPrincipal_smooth_at g hg p x (hp _) J hJe i j).comp x
        (contDiffAt_const.prodMk contDiffAt_id))).contDiffWithinAt
  have hB (j : Fin 4) : ContDiffOn ℝ ∞ (complexDrift g w j p) U := by
    intro x hx
    obtain ⟨J,hJe⟩ := hJ x hx
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((chartDrift_smooth_at g hg w hw p x (hp _) (hwp x hx) J hJe j).comp x
        (contDiffAt_const.prodMk contDiffAt_id))).contDiffWithinAt
  unfold smoothSecondOrder
  exact ((ContDiffOn.sum (fun i _ ↦ ContDiffOn.sum (fun j _ ↦
    (hG i j).mul (coordPartial_contDiff (coordPartial_contDiff hu j) i).contDiffOn))).add
      (ContDiffOn.sum (fun i _ ↦ (hB i).mul (coordPartial_contDiff hu i).contDiffOn))).add
        (contDiffOn_const.mul hu.contDiffOn)

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

lemma gaussian_source_euclidean (x : _root_.OAI.Yau.Jets.Coord) (c N s : ℝ) (hc : 0 ≤ c) (hN : 0 ≤ N) :
    Real.exp (N*s-c*N*‖x‖^2) ≤ Real.exp (N*s-(c/4)*N*(sourceEuclideanNorm x)^2) := by
  have h := gaussian_chart_norm_bound c N 2 ‖x‖ (sourceEuclideanNorm x) hc hN (by norm_num)
    (norm_nonneg _) (sourceEuclideanNorm_nonneg x) (sourceEuclideanNorm_le x)
  apply Real.exp_le_exp.mpr
  norm_num at h
  linarith

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

lemma scaledCutoff_contDiff (N : ℝ) (y : E) : ContDiff ℝ ∞ (scaledCutoff N y) :=
  (baseCutoff (E := E)).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)

theorem scaledCutoff_support {N : ℝ} (hN : 0 < N) (y : E) :
    Function.support (scaledCutoff N y) = Metric.ball y (2 * N ^ (-1 / 3 : ℝ)) := by
  ext x
  change (baseCutoff (E := E)) (N ^ (1 / 3 : ℝ) • (x - y)) ≠ 0 ↔ _
  rw [← Function.mem_support, (baseCutoff (E := E)).support_eq]
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hN _)]
  change N ^ (1 / 3 : ℝ) * ‖x - y‖ < 2 ↔ ‖x - y‖ < 2 * N ^ (-1 / 3 : ℝ)
  rw [mul_comm, ← lt_div_iff₀ (Real.rpow_pos_of_pos hN _)]
  have he : N ^ (-1 / 3 : ℝ) = (N ^ (1 / 3 : ℝ))⁻¹ := by
    rw [show (-1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring, Real.rpow_neg hN.le]
  rw [he, div_eq_mul_inv]

end
end Yau.Waves

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ConstructedCoordinateWaves
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

omit [TopologicalSpace T] [CompactSpace T] in
lemma coordinateWave_smooth (phi : T → CPoly) (A : ℕ → T → CPoly) (J : ℕ) (N : ℝ) (t : T) :
    ContDiff ℝ ∞ (coordinateWave phi A J N t) :=
  (Yau.Waves.scaledCutoff_contDiff N (0:_root_.OAI.Yau.Jets.Coord)).smul
    ((finiteAmplitude_contDiff _ _ _).mul (waveExp_contDiff (reval_contDiff _) N))

omit [TopologicalSpace T] [CompactSpace T] in
lemma coordinateWave_support (phi : T → CPoly) (A : ℕ → T → CPoly) (J : ℕ) (N : ℝ)
    (hN : 0 < N) (t : T) :
    tsupport (coordinateWave phi A J N t) ⊆ Metric.closedBall 0 (2*N^(-1/3:ℝ)) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hb : Yau.Waves.scaledCutoff N (0:_root_.OAI.Yau.Jets.Coord) x ≠ 0 := by
    intro hz
    exact hx (by simp [coordinateWave,hz])
  have hh : x ∈ Function.support (Yau.Waves.scaledCutoff N (0:_root_.OAI.Yau.Jets.Coord)) := hb
  rw [Yau.Waves.scaledCutoff_support hN] at hh
  exact Metric.ball_subset_closedBall hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_UniformChartWaveTransfer
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set Metric
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem uniform_chart_wave_transfer
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : T → QuadParam _root_.OAI.Yau.Jets.Coord) (hpc : Continuous p)
    (F : T → OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord)
    (hF : ∀ t, (F t : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = rawQuadratic (p t))
    (r : ℝ) (hr : 0 < r) (hsource : ∀ t, (F t).source = ball 0 r)
    (hInv : ∀ t, ContDiffOn ℝ ∞ (F t).symm (F t).target)
    (hJ : ∀ t, ∀ x ∈ (F t).source, ∃ J : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      fderiv ℝ (rawQuadratic (p t)) x = J.toContinuousLinearMap)
    (hwp : ∀ t, ∀ z ∈ (F t).target, 0 < w z)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (u : ℕ → T → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hu : ∀ n t, ContDiff ℝ ∞ (u n t))
    (hsupport : ∀ n, 0 < n → ∀ t, tsupport (u n t) ⊆ closedBall 0 (2*(n:ℝ)^(-1/3:ℝ)))
    (k0 K : ℕ) (c Cr : ℝ) (Cs : Fin (k0+1) → ℝ)
    (hc : 0 < c) (hCr : 0 < Cr) (hCs : ∀ k, 0 < Cs k)
    (hest : ∀ᶠ n : ℕ in atTop, ∀ t x,
      (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (u n t) x‖ ≤
        Cs k*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)-c*(n:ℝ)*‖x‖^2)) ∧
      DerivativeBound k0 (fun z ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j (p t))
        (fun j ↦ complexDrift g w j (p t)) (u n t) z +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*u n t z) x
        (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)))) :
    ∃ c' Cw Cr' R : ℝ, 0 < c' ∧ 0 < Cw ∧ 0 < Cr' ∧ 0 < R ∧
      ∀ᶠ n : ℕ in atTop, ∀ t,
        ContDiff ℝ ∞ (chartPushforward (F t) (u n t)) ∧
        HasCompactSupport (chartPushforward (F t) (u n t)) ∧
        tsupport (chartPushforward (F t) (u n t)) ⊆ closedBall (p t).1 (R*(n:ℝ)^(-1/3:ℝ)) ∧
        ∀ z : _root_.OAI.Yau.Jets.Coord,
          (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (chartPushforward (F t) (u n t)) z‖ ≤
            Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c'*(n:ℝ)*‖z-(p t).1‖^2)) ∧
          DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w (chartPushforward (F t) (u n t)) z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*chartPushforward (F t) (u n t) z) z
              (Cr'*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z)) := by
  have hR (t : T) : closedBall (0:_root_.OAI.Yau.Jets.Coord) (r/2) ⊆ (F t).source := by
    rw [hsource t]
    exact closedBall_subset_ball (by linarith)
  obtain ⟨D,hD,hDb⟩ := compact_inverse_derivative_bounds isCompact_univ p hpc F
    (fun t _ ↦ hF t) (fun t _ ↦ hInv t) (fun t _ ↦ hJ t) (r/2) (fun t _ ↦ hR t) k0
  obtain ⟨L,hL,hLb⟩ := compact_chart_norm_bound isCompact_univ p hpc (r/2) (by positivity)
  let Ct : ℝ := ∑ k, Cs k
  have hCt : 0 < Ct := Finset.sum_pos (fun k _ ↦ hCs k) Finset.univ_nonempty
  have hCi (k : Fin (k0+1)) : Cs k ≤ Ct :=
    Finset.single_le_sum (fun j _ ↦ (hCs j).le) (Finset.mem_univ k)
  let Q : ℝ := (k0.factorial : ℝ)*D^k0
  have hQ : 0 < Q := by dsimp [Q] <;> positivity
  have hQk (k : ℕ) (hk : k ≤ k0) : (k.factorial:ℝ)*D^k ≤ Q := by
    have hf : (k.factorial:ℝ) ≤ k0.factorial := by exact_mod_cast Nat.factorial_le hk
    have hd := pow_le_pow_right₀ hD hk
    dsimp [Q]
    gcongr
  refine ⟨c/L^2,Q*Ct,Q*Cr,2*L,by positivity,mul_pos hQ hCt,mul_pos hQ hCr,by positivity,?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, 2*(n:ℝ)^(-1/3:ℝ) < r/2 := by
    apply eventually_nat_frequency (P := fun N : ℝ ↦ 2*N^(-1/3:ℝ) < r/2)
    have ht : Tendsto (fun N : ℝ ↦ 2*N^(-1/3:ℝ)) atTop (𝓝 0) := by
      simpa only [neg_div,mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul 2
    exact ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hest,hsmall,eventually_ge_atTop (1:ℕ)] with n hn hsmall hn1
  have hnpos : 0 < n := by omega
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn1
  intro t
  have hus := hsupport n hnpos t
  have huR : tsupport (u n t) ⊆ closedBall (0:_root_.OAI.Yau.Jets.Coord) (r/2) :=
    hus.trans (closedBall_subset_closedBall hsmall.le)
  have huSource := huR.trans (hR t)
  have huComp : HasCompactSupport (u n t) :=
    (isCompact_closedBall (0:_root_.OAI.Yau.Jets.Coord) (r/2)).of_isClosed_subset isClosed_closure huR
  obtain ⟨hVs,hVc,hVsup⟩ := chartPushforward_smooth (F t) (hInv t) (u n t) (hu n t) huComp huSource
  refine ⟨hVs,hVc,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := hVsup hz
    have hnorm := hLb t (mem_univ t) x (huR hx)
    have hxN : ‖x‖ ≤ 2*(n:ℝ)^(-1/3:ℝ) := by simpa using hus hx
    rw [mem_closedBall,dist_eq_norm,hF t]
    calc
      _ ≤ L*‖x‖ := hnorm
      _ ≤ L*(2*(n:ℝ)^(-1/3:ℝ)) := mul_le_mul_of_nonneg_left hxN (by positivity)
      _ = _ := by ring
  · intro z
    by_cases hz : z ∈ tsupport (chartPushforward (F t) (u n t))
    · obtain ⟨x,hx,rfl⟩ := hVsup hz
      have hxS := huSource hx
      have hxt := (F t).map_source hxS
      have hinv : (F t).symm (F t x) = x := (F t).left_inv hxS
      have hFx : rawQuadratic (p t) x = F t x := congrFun (hF t).symm x
      have hdi (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k0) := hDb t (mem_univ t) x (huR hx) i hi hik
      have hnorm : ‖F t x-(p t).1‖ ≤ L*‖x‖ := by rw [hF t]; exact hLb t (mem_univ t) x (huR hx)
      have hgauss : Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)-c*(n:ℝ)*‖x‖^2) ≤
          Real.exp ((n:ℝ)*S (F t x)-(c/L^2)*(n:ℝ)*‖F t x-(p t).1‖^2) := by
        apply Real.exp_le_exp.mpr
        rw [hFx]
        have hh := gaussian_chart_norm_bound c (n:ℝ) L ‖x‖ ‖F t x-(p t).1‖ hc.le
          (by positivity) (by positivity) (norm_nonneg _) (norm_nonneg _) hnorm
        linarith
      refine ⟨?_,?_⟩
      · intro k
        have hk : k.val ≤ k0 := by omega
        have hb := chart_wave_size_transfer (F t) (hInv t) (u n t) (hu n t) (F t x) hxt k.val
          Ct D (Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)-c*(n:ℝ)*‖x‖^2)) (n:ℝ)
          hCt.le (by positivity) hN (fun i hi ↦ by
            rw [hinv]
            have hh := (hn t x).1 ⟨i,by omega⟩
            exact hh.trans (by gcongr; exact hCi ⟨i,by omega⟩))
          (fun i hi hik ↦ hdi i hi (hik.trans hk))
        apply hb.trans
        have hq := hQk k.val hk
        calc
          _ = ((k.val.factorial:ℝ)*D^k.val)*Ct*(n:ℝ)^k.val*
              Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)-c*(n:ℝ)*‖x‖^2) := by ring
          _ ≤ _ := by gcongr
      · intro k hk
        rw [transported_residual_derivative g hg hp w hw (p t) (F t) (hF t) (hInv t) (hJ t)
          (hwp t) (u n t) (hu n t) huComp huSource _ (F t x) hxt k]
        have hrs := actual_coordinate_residual_smoothOn g hg hp w hw (p t) (F t).source (hJ t)
          (fun x hx ↦ by rw [← hF t]; exact hwp t (F t x) ((F t).map_source hx)) (u n t) (hu n t)
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))
        have hb := chart_residual_bound_transfer (F t) (hInv t) _ hrs (F t x) hxt k
          Cr D (Real.exp ((n:ℝ)*S (rawQuadratic (p t) x))) (n:ℝ) (K:ℝ)
          (fun i hi ↦ by rw [hinv]; exact (hn t x).2 i (hi.trans hk))
          (fun i hi hik ↦ hdi i hi (hik.trans hk))
        apply hb.trans
        rw [hFx]
        have hq := hQk k hk
        calc
          _ = ((k.factorial:ℝ)*D^k)*Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S (F t x)) := by ring
          _ ≤ _ := by gcongr
    · have he : chartPushforward (F t) (u n t) =ᶠ[𝓝 z] (fun _ ↦ 0) :=
        notMem_tsupport_iff_eventuallyEq.mp hz
      refine ⟨?_,?_⟩
      · intro k
        rw [(he.iteratedFDeriv ℝ k.val).self_of_nhds]
        have hzder : iteratedFDeriv ℝ k.val (fun _ : _root_.OAI.Yau.Jets.Coord ↦ (0:ℂ)) z = 0 := by simp
        rw [hzder,norm_zero]
        positivity
      · intro k _
        rw [source_residual_derivative_zero g w _ _ z hz k]
        simp only [norm_zero]
        positivity

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ConstructedSourceWavesLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets Filter Set
open scoped ContDiff Topology
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem witnessed_source_wave_estimates
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (q : T → _root_.OAI.Yau.Jets.Coord) (a bb : T → ℝ) (ha : Continuous a) (hbb : Continuous bb)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0) (hlen : ∀ t, bb t^2 = a t^2+4)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, bb t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t, 0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t)) +
      sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ (beta : ContDiffBump (0:_root_.OAI.Yau.Jets.Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly)
      (F : T → OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord) (c Cw Cr R r d : ℝ),
      0 < c ∧ 0 < Cw ∧ 0 < Cr ∧ 0 < R ∧ 0 < r ∧ 0 < d ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      (∀ t, (F t : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = actualMetricChart g (y t) (e t)) ∧
      (∀ t, (F t).source = Metric.ball 0 r ∧ Metric.closedBall (y t) d ⊆ (F t).target ∧
        ContDiffOn ℝ ∞ (F t).symm (F t).target) ∧
      ∀ᶠ n : ℕ in atTop, ∀ t,
        let V := chartPushforward (F t) (coordinateWave phi A J (n:ℝ) t)
        ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
        tsupport V ⊆ Metric.closedBall (y t) (R*(n:ℝ)^(-1/3:ℝ)) ∧
        ∀ z : _root_.OAI.Yau.Jets.Coord,
          (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val V z‖ ≤
            Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c*(n:ℝ)*‖z-y t‖^2)) ∧
          DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w V z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*V z) z
              (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z)) := by
  have hB := actualFrameConnection_continuous g hg hpos y hy e he
  obtain ⟨r,hr,d,hd,hcharts⟩ := compact_invariant_charts isCompact_univ g hg hpos w hw y hy e he
    (fun t ↦ actualFrameConnection g (y t) (e t)) hB hU (fun t _ ↦ hyU t) hwpos
  have hcharts' := fun t ↦ hcharts t (mem_univ t)
  choose F hFe hFs hFt hFU hInv hJac hOp using hcharts'
  obtain ⟨beta,phi,A,c,Cr,Cs,hc,hCr,hCs,hjets,hest⟩ := constructed_coordinate_wave_estimates
    g hg hs hpos w hw S hS y hy e he ho hU hyU hwpos q a bb ha hbb ha0 hb0 hlen hap hbq hstrict
    m J K k0 hm hJ
  have hpc : Continuous (fun t ↦ metricChartParameter g (y t) (e t)) := hy.prodMk (he.prodMk hB)
  obtain ⟨c',Cw,Cr',R,hc',hCw,hCr',hR,hsource⟩ := uniform_chart_wave_transfer
    g hg hpos w hw (fun t ↦ metricChartParameter g (y t) (e t)) hpc F hFe r hr hFs hInv hJac
    (fun t z hz ↦ hwpos z (hFU t hz)) S (fun n t ↦ coordinateWave phi A J (n:ℝ) t)
    (fun n t ↦ coordinateWave_smooth phi A J (n:ℝ) t)
    (fun n hn t ↦ coordinateWave_support phi A J (n:ℝ) (by exact_mod_cast hn) t)
    k0 K c Cr Cs hc hCr hCs hest
  exact ⟨beta,phi,A,F,c',Cw,Cr',R,r,d,hc',hCw,hCr',hR,hr,hd,hjets,hFe,
    (fun t ↦ ⟨hFs t,hFt t,hInv t⟩),hsource⟩

end Yau.Geometry

end

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
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WitnessedEuclideanWaves
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem witnessed_source_wave_estimates_euclidean
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (q : T → _root_.OAI.Yau.Jets.Coord) (a bb : T → ℝ) (ha : Continuous a) (hbb : Continuous bb)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0) (hlen : ∀ t, bb t^2 = a t^2+4)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, bb t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t, 0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t)) +
      sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ (beta : ContDiffBump (0:_root_.OAI.Yau.Jets.Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly)
      (F : T → OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord) (c Cw Cr R r d : ℝ),
      0 < c ∧ 0 < Cw ∧ 0 < Cr ∧ 0 < R ∧ 0 < r ∧ 0 < d ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      (∀ t, (F t : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = actualMetricChart g (y t) (e t)) ∧
      (∀ t, (F t).source = Metric.ball 0 r ∧ Metric.closedBall (y t) d ⊆ (F t).target ∧
        ContDiffOn ℝ ∞ (F t).symm (F t).target) ∧
      ∀ᶠ n : ℕ in atTop, ∀ t,
        let V := chartPushforward (F t) (coordinateWave phi A J (n:ℝ) t)
        ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
        tsupport V ⊆ {z | sourceEuclideanNorm (z-y t) ≤ R*(n:ℝ)^(-1/3:ℝ)} ∧
        ∀ z : _root_.OAI.Yau.Jets.Coord,
          (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val V z‖ ≤
            Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c*(n:ℝ)*(sourceEuclideanNorm (z-y t))^2)) ∧
          DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w V z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*V z) z
              (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z)) := by
  obtain ⟨beta,phi,A,F,c,Cw,Cr,R,r,d,hc,hCw,hCr,hR,hr,hd,hjets,hFe,hdom,hest⟩ := witnessed_source_wave_estimates
    g hg hs hpos w hw S hS y hy e he ho hU hyU hwpos q a bb ha hbb ha0 hb0 hlen hap hbq hstrict
    m J K k0 hm hJ
  refine ⟨beta,phi,A,F,c/4,Cw,Cr,2*R,r,d,by positivity,hCw,hCr,by positivity,hr,hd,hjets,hFe,hdom,?_⟩
  filter_upwards [hest] with n hn
  intro t
  obtain ⟨hsm,hcomp,hsup,hbounds⟩ := hn t
  refine ⟨hsm,hcomp,?_,?_⟩
  · intro z hz
    have hzsup : ‖z-y t‖ ≤ R*(n:ℝ)^(-1/3:ℝ) := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hsup hz
    calc
      _ ≤ 2*‖z-y t‖ := sourceEuclideanNorm_le _
      _ ≤ 2*(R*(n:ℝ)^(-1/3:ℝ)) := mul_le_mul_of_nonneg_left hzsup (by norm_num)
      _ = _ := by ring
  · intro z
    refine ⟨?_,(hbounds z).2⟩
    intro k
    apply ((hbounds z).1 k).trans
    have he := gaussian_source_euclidean (z-y t) c (n:ℝ) (S z) hc.le (by positivity)
    exact mul_le_mul_of_nonneg_left he (by positivity)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_TripleSourceWaves
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem construct_triple_source_waves_oai
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (d : SourceFrameTriple g S y) {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    Nonempty (TripleSourceWaveData g w S y d m J K k0) := by
  have hp : Continuous (fun z : T × Fin 3 ↦ metricGradient g S (y z.1)) := (metricGradient_continuous g hg hpos S hS).comp (hy.comp continuous_fst)
  have hlen : Continuous (fun z : T × Fin 3 ↦
      g (y z.1) (metricGradient g S (y z.1)) (metricGradient g S (y z.1))) :=
    (((hg.continuous.comp (hy.comp continuous_fst)).clm_apply hp).clm_apply hp)
  have hapos (z : T × Fin 3) : 0 < sourceTripleAlpha g S y z :=
    Real.sqrt_pos.mpr (hpos (y z.1) _ (hp0 z.1))
  have hbpos (z : T × Fin 3) : 0 < sourceTripleBeta g S y z := by
    apply Real.sqrt_pos.mpr
    have h := hpos (y z.1) _ (hp0 z.1)
    linarith
  have hab (z : T × Fin 3) : (sourceTripleBeta g S y z)^2 = (sourceTripleAlpha g S y z)^2+4 := by
    dsimp [sourceTripleAlpha,sourceTripleBeta]
    rw [Real.sq_sqrt (hpos (y z.1) _ (hp0 z.1)).le,Real.sq_sqrt]
    have h := hpos (y z.1) _ (hp0 z.1)
    linarith
  obtain ⟨beta,phi,A,F,c,Cw,Cr,R,r,delta,hc,hCw,hCr,hR,hr,hdelta,hjets,hF,hdom,hest⟩ :=
    witnessed_source_wave_estimates_euclidean g hg hs hpos w hw S hS
      (fun z : T × Fin 3 ↦ y z.1) (hy.comp continuous_fst) d.frame d.continuous_frame
      d.frame_orthonormal hU (fun z ↦ hyU z.1) hwpos (fun z ↦ d.q z.1 z.2)
      (sourceTripleAlpha g S y) (sourceTripleBeta g S y) hlen.sqrt (hlen.add continuous_const).sqrt
      (fun z ↦ ne_of_gt (hapos z)) (fun z ↦ ne_of_gt (hbpos z)) hab
      (d.frame_first (fun t ↦ hpos (y t)) hp0) (d.frame_second (fun t ↦ hpos (y t)) hp0)
      (fun z ↦ d.strict z.1 z.2) m J K k0 hm hJ
  exact ⟨⟨beta,phi,A,F,c,Cw,Cr,R,hc,hCw,hCr,hR,r,delta,hr,hdelta,hjets,hF,hdom,hest⟩⟩

end
end Yau.Geometry

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Yau.Geometry.construct_triple_source_waves_oai.{u_1} := @OAI.Yau.Geometry.construct_triple_source_waves_oai.{u_1}
