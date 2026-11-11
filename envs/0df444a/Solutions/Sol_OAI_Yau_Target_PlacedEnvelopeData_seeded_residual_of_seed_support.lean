-- Prove2me | solution 1 for OAI.Yau.Target.PlacedEnvelopeData.seeded_residual_of_seed_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:31:20.858998+00:00
-- url     : https://prove2.me/submissions/a9135d42-c657-4a32-9ada-c36a0fefc573

import Mathlib
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
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_PlacedEnvelopeData_waves_in_domain

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

lemma coordPartial_mul {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (i : Fin 4) : coordPartial i (fun x ↦ f x * u x) =
      fun x ↦ coordPartial i f x * u x + f x * coordPartial i u x := by
  funext x
  unfold coordPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hu.differentiable (by simp) x)]
  simp [smul_eq_mul]
  ring

lemma coordPartial_const_mul {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (a : ℂ) (i : Fin 4) :
    coordPartial i (fun x ↦ a * f x) = fun x ↦ a * coordPartial i f x := by
  rw [coordPartial_mul contDiff_const hf]
  ext x
  simp [coordPartial]

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

lemma coordPartial_ofReal_at (f : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ (f z : ℂ)) x = (fderiv ℝ f x (Pi.single i 1) : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x (Pi.single i 1) = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

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

end
end Yau.Geometry

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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_r8b039c_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
lemma seedQuadratic_contDiff : ContDiff ℝ ∞ seedQuadratic :=
  seedZ1.contDiff.mul seedZ2.contDiff

lemma ambientComplexSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientComplexSeed N) :=
  seedQuadratic_contDiff.pow N

lemma ambientRealSeed_contDiff (N : ℕ) : ContDiff ℝ ∞ (ambientRealSeed N) :=
  Complex.reCLM.contDiff.comp (ambientComplexSeed_contDiff N)

lemma seedEigenvalue_pos {N : ℕ} (hN : 0 < N) : 0 < seedEigenvalue N := by
  unfold seedEigenvalue
  have : (0:ℝ) < N := by exact_mod_cast hN
  positivity

end
end Yau.Target

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

theorem compact_positive_metric_extension {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v) :
    ∃ G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ,
      ContDiff ℝ ∞ G ∧ (∀ x u v, G x u v = G x v u) ∧
      (∀ x v, v ≠ 0 → 0 < G x v v) ∧ ∀ x ∈ K, G =ᶠ[𝓝 x] g := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  obtain ⟨x0,hx0⟩ := hUn
  let G := fun x ↦ b x • g x + (1-b x) • g x0
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact (hb.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds (hbU hx)))).add
        ((contDiffAt_const.sub hb.contDiffAt).smul contDiffAt_const)
    · apply (contDiffAt_const (c := g x0)).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
      simp [G,hz]
  refine ⟨G,hG,?_,?_,?_⟩
  · intro x u v
    by_cases hx : x ∈ tsupport b
    · change b x*g x u v+(1-b x)*g x0 u v = b x*g x v u+(1-b x)*g x0 v u
      rw [hs x (hbU hx),hs x0 hx0]
    · simp [G,image_eq_zero_of_notMem_tsupport hx,hs x0 hx0]
  · intro x v hv
    by_cases hx : x ∈ tsupport b
    · have h1 := hp x (hbU hx) v hv
      have h2 := hp x0 hx0 v hv
      have hb0 := (hbr x).1
      have hb1 := (hbr x).2
      change 0 < b x*g x v v+(1-b x)*g x0 v v
      by_cases hz : b x = 0
      · simpa [hz] using h2
      · have ha : 0 < b x := lt_of_le_of_ne hb0 (Ne.symm hz)
        have hleft := mul_pos ha h1
        have hright := mul_nonneg (sub_nonneg.mpr hb1) h2.le
        linarith
    · simpa [G,image_eq_zero_of_notMem_tsupport hx] using hp x0 hx0 v hv
  · intro x hx
    filter_upwards [hb1 x hx] with z hz
    simp [G,hz]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSourceRepresentatives
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

theorem compact_source_representatives {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w S : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hS : ContDiffOn ℝ ∞ S U)
    (hwp : ∀ x ∈ U, 0 < w x) :
    ∃ (G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (W A : _root_.OAI.Yau.Jets.Coord → ℝ) (E : Set _root_.OAI.Yau.Jets.Coord),
      ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ W ∧ ContDiff ℝ ∞ A ∧
      (∀ x u v, G x u v = G x v u) ∧ (∀ x v, v ≠ 0 → 0 < G x v v) ∧
      IsOpen E ∧ K ⊆ E ∧ E ⊆ U ∧ (∀ x ∈ E, 0 < W x) ∧
      ∀ x ∈ E, (G =ᶠ[𝓝 x] g) ∧ (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S) ∧
        metricGradient G A x = metricGradient g S x ∧ sourceHessian G A x = sourceHessian g S x := by
  obtain ⟨G,hG,hGs,hGp,hGe⟩ := compact_positive_metric_extension hK hU hKU hUn g hg hs hp
  obtain ⟨W,hW,_,_,hWe⟩ := compact_smooth_extension hK hU hKU w hw
  obtain ⟨A,hA,_,_,hAe⟩ := compact_smooth_extension hK hU hKU S hS
  let B : Set _root_.OAI.Yau.Jets.Coord := {x | G x = g x ∧ W x = w x ∧ A x = S x}
  let E := U ∩ interior B
  have hE : IsOpen E := hU.inter isOpen_interior
  have hKE : K ⊆ E := by
    intro x hx
    refine ⟨hKU hx,mem_interior_iff_mem_nhds.mpr ?_⟩
    exact (hGe x hx).and ((hWe x hx).and (hAe x hx))
  have hgerm (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ E) : (G =ᶠ[𝓝 x] g) ∧
      (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S) := by
    have hh : ∀ᶠ z in 𝓝 x, G z = g z ∧ W z = w z ∧ A z = S z :=
      mem_of_superset (hE.mem_nhds hx) (fun z hz ↦ interior_subset hz.2)
    exact ⟨hh.mono (fun _ h ↦ h.1),hh.mono (fun _ h ↦ h.2.1),hh.mono (fun _ h ↦ h.2.2)⟩
  refine ⟨G,W,A,E,hG,hW,hA,hGs,hGp,hE,hKE,inter_subset_left,?_,?_⟩
  · intro x hx
    rw [(hgerm x hx).2.1.self_of_nhds]
    exact hwp x hx.1
  · intro x hx
    obtain ⟨heG,heW,heA⟩ := hgerm x hx
    exact ⟨heG,heW,heA,(metricGradient_eventuallyEq heG heA).self_of_nhds,
      (sourceHessian_eventuallyEq heG heA).self_of_nhds⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ExponentialWaveBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma norm_iteratedFDeriv_complex_exp (k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k Complex.exp z‖ = Real.exp z.re := by
  have he := (Complex.contDiff_exp (𝕜 := ℂ) (n := k)).contDiffAt.restrictScalars_iteratedFDeriv
    (𝕜 := ℝ) (x := z)
  rw [← he]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hd : iteratedDeriv k Complex.exp z = Complex.exp z := by
    simpa using congrFun (iteratedDeriv_cexp_const_mul k 1) z
  rw [hd, Complex.norm_exp]

theorem waveExp_derivative_bound {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (k : ℕ) (x : Coord) {D N : ℝ} (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hphi : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i phi x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (waveExp phi N) x‖ ≤
      (k.factorial : ℝ) * D ^ k * N ^ k * Real.exp (N * (phi x).re) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hDN : 1 ≤ D * N := one_le_mul_of_one_le_of_one_le hD hN
  have hb : ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i (fun z ↦ (N : ℂ) * phi z) x‖ ≤ (D * N) ^ i := by
    intro i hi hik
    change ‖iteratedFDeriv ℝ i (fun z ↦ (N : ℂ) • phi z) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hp.of_le (by
      exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top))).contDiffAt, norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp]
    calc
      _ ≤ N * D := mul_le_mul_of_nonneg_left (hphi i hi hik) hNp.le
      _ = (D * N) ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hDN hi
  have he := norm_iteratedFDeriv_comp_le
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)) (contDiff_const.mul hp) (n := k)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)) x
    (fun i _ ↦ le_of_eq (norm_iteratedFDeriv_complex_exp i ((N : ℂ) * phi x))) hb
  change ‖iteratedFDeriv ℝ k (fun z ↦ Complex.exp ((N : ℂ) * phi z)) x‖ ≤ _
  simpa [Function.comp_def, mul_pow, mul_assoc, mul_left_comm, mul_comm] using he

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveSize
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma mul_derivative_power_bound {f u : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : Coord)
    {A B N w : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hfa : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ A * N ^ j)
    (hub : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j u x‖ ≤ B * N ^ j * w) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f z * u z) x‖ ≤ (2 : ℝ) ^ k * A * B * N ^ k * w := by
  have h := norm_iteratedFDeriv_mul_le hf hu x (n := k)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  calc
    _ ≤ _ := h
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (A * B * N ^ k * w) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
      have hm := mul_le_mul (hfa j hjk) (hub (k - j) (Nat.sub_le _ _))
        (norm_nonneg _) (mul_nonneg hA (pow_nonneg hN _))
      have he : (A * N ^ j) * (B * N ^ (k - j) * w) = A * B * N ^ k * w := by
        rw [show (A * N ^ j) * (B * N ^ (k - j) * w) =
          A * B * (N ^ j * N ^ (k - j)) * w by ring, ← pow_add, Nat.add_sub_of_le hjk]
      rw [he] at hm
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (k.choose j))
    _ = _ := by
      rw [← Finset.sum_mul]
      have he : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ) ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [he]
      ring

end
end Yau.Jets

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

lemma DerivativeBound.mono {k l : ℕ} {f : Coord → ℂ} {x : Coord} {C : ℝ}
    (h : DerivativeBound k f x C) (hl : l ≤ k) : DerivativeBound l f x C :=
  fun j hj ↦ h j (hj.trans hl)

lemma DerivativeBound.mul {k : ℕ} {f g : Coord → ℂ} {x : Coord} {A B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : DerivativeBound k f x A) (hb : DerivativeBound k g x B) :
    DerivativeBound k (fun z ↦ f z * g z) x (2 ^ k * A * B) := by
  intro j hj
  have h := mul_derivative_power_bound hf hg j x hA (by norm_num : (0:ℝ) ≤ 1)
    (N := 1) (w := 1) (fun i hi ↦ by simpa using ha i (hi.trans hj))
    (fun i hi ↦ by simpa using hb i (hi.trans hj))
  simp only [one_pow, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB)

lemma DerivativeBound.sum {ι : Type*} (s : Finset ι) {k : ℕ}
    {f : ι → Coord → ℂ} {x : Coord} {C : ι → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ s, DerivativeBound k (f i) x (C i)) :
    DerivativeBound k (fun z ↦ ∑ i ∈ s, f i z) x (∑ i ∈ s, C i) := by
  intro j hj
  rw [iteratedFDeriv_fun_sum_apply (fun i hi ↦ ((hf i hi).of_le
    (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi ↦ hb i hi j hj))

lemma coordPartial_derivative_norm_le (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (i : Fin 4) (k : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ k (coordPartial i f) x‖ ≤ ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  let L : (Coord →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (Pi.single i 1)
  have he : coordPartial i f = L ∘ fderiv ℝ f := rfl
  have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [he, L.iteratedFDeriv_comp_left hf'.contDiffAt
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro v
      have h := v.le_opNorm (Pi.single i (1 : ℝ))
      have hn : ‖(Pi.single i (1 : ℝ) : Coord)‖ ≤ 1 := by
        apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
        intro j
        by_cases hij : j = i <;> simp [hij]
      exact h.trans (by simpa using mul_le_mul_of_nonneg_left hn (norm_nonneg v))
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

lemma DerivativeBound.coordPartial {k : ℕ} {f : Coord → ℂ} {x : Coord} {C : ℝ}
    (hf : ContDiff ℝ ∞ f) (h : DerivativeBound (k+1) f x C) (i : Fin 4) :
    DerivativeBound k (coordPartial i f) x C := by
  intro j hj
  exact (coordPartial_derivative_norm_le f hf i j x).trans (h (j+1) (by omega))

end
end Yau.Jets

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

lemma gaussianWaveField_iterated_bound (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (a : ι × Fin 2 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (k : ℕ) (x : _root_.OAI.Yau.Jets.Coord) {R B : ℝ}
    (hR : 0 ≤ R) (ha : a ∈ coefficientEvent R)
    (hB : ∀ i, ‖iteratedFDeriv ℝ k (V i) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (gaussianWaveField V a) x‖ ≤ (Fintype.card ι:ℝ)*R*B := by
  classical
  let W : _root_.OAI.Yau.Jets.Coord → ℂ := fun z ↦ ∑ i, gaussianCoefficient a i*V i z
  have hW : ContDiff ℝ ∞ W := ContDiff.sum (fun i _ ↦ contDiff_const.mul (hV i))
  have hr := realPart_iterated_norm_le W x hW.contDiffAt k
  change ‖iteratedFDeriv ℝ k (gaussianWaveField V a) x‖ ≤ _ at hr
  refine hr.trans ?_
  dsimp only [W]
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
    ((contDiff_const.mul (hV i)).of_le
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  refine (norm_sum_le _ _).trans ?_
  have hb (i : ι) : ‖iteratedFDeriv ℝ k (fun z ↦ gaussianCoefficient a i*V i z) x‖ ≤ R*B := by
    change ‖iteratedFDeriv ℝ k (gaussianCoefficient a i • V i) x‖ ≤ R*B
    rw [iteratedFDeriv_const_smul_apply ((hV i).of_le
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,norm_smul]
    exact (mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hB i) hR)
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ hb i)
  simpa [mul_assoc] using hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteLinearity
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
variable {ι : Type*} [Fintype ι]

lemma coordPartial_finite_sum (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hV : ∀ a, Differentiable ℝ (V a)) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (fun x ↦ ∑ a, V a x) = fun x ↦ ∑ a, _root_.OAI.Yau.Jets.coordPartial i (V a) x := by
  funext x
  simp only [_root_.OAI.Yau.Jets.coordPartial, fderiv_fun_sum (fun a _ ↦ hV a x),
    sum_apply]

lemma coordPartial_real_projection (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : Differentiable ℝ u) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (fun x ↦ ((u x).re : ℂ)) = fun x ↦ ((_root_.OAI.Yau.Jets.coordPartial i u x).re : ℂ) := by
  funext x
  have hr : DifferentiableAt ℝ (fun z ↦ (u z).re) x :=
    Complex.reCLM.differentiableAt.comp x (hu x)
  rw [coordPartial_ofReal_at (fun z ↦ (u z).re) x hr,
    realPart_fderiv u x (hu x)]
  rfl

lemma sourceFlux_finite_sum
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (hV : ∀ a, Differentiable ℝ (V a)) (i : Fin 4) :
    sourceFlux g w (fun x ↦ ∑ a, V a x) i = fun x ↦ ∑ a, sourceFlux g w (V a) i x := by
  funext x
  simp only [sourceFlux, coordPartial_finite_sum V hV, Finset.mul_sum]
  exact Finset.sum_comm

lemma sourceFlux_const_mul
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (c : ℂ) (i : Fin 4) :
    sourceFlux g w (fun x ↦ c*u x) i = fun x ↦ c*sourceFlux g w u i x := by
  funext x
  simp only [sourceFlux, coordPartial_const_mul hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sourceFlux_real_projection
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : Differentiable ℝ u) (i : Fin 4) :
    sourceFlux g w (fun x ↦ ((u x).re:ℂ)) i = fun x ↦ ((sourceFlux g w u i x).re:ℂ) := by
  funext x
  simp [sourceFlux,coordPartial_real_projection u hu,Complex.mul_re]

lemma sourceWeightedOperator_finite_sum
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (hV : ∀ a, Differentiable ℝ (V a))
    (hf : ∀ a i, Differentiable ℝ (sourceFlux g w (V a) i)) :
    sourceWeightedOperator g w (fun x ↦ ∑ a, V a x) =
      fun x ↦ ∑ a, sourceWeightedOperator g w (V a) x := by
  funext x
  simp only [sourceWeightedOperator,complexDivergence,sourceFlux_finite_sum g w V hV,
    coordPartial_finite_sum _ (fun a ↦ hf a _),Finset.mul_sum]
  exact Finset.sum_comm

lemma sourceWeightedOperator_const_mul
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u)
    (hf : ∀ i, ContDiff ℝ ∞ (sourceFlux g w u i)) (c : ℂ) :
    sourceWeightedOperator g w (fun x ↦ c*u x) = fun x ↦ c*sourceWeightedOperator g w u x := by
  funext x
  simp only [sourceWeightedOperator,complexDivergence,sourceFlux_const_mul g w u hu,
    coordPartial_const_mul (hf _),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma sourceWeightedOperator_real_projection
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : Differentiable ℝ u)
    (hf : ∀ i, Differentiable ℝ (sourceFlux g w u i)) :
    sourceWeightedOperator g w (fun x ↦ ((u x).re:ℂ)) =
      fun x ↦ ((sourceWeightedOperator g w u x).re:ℂ) := by
  funext x
  simp [sourceWeightedOperator,complexDivergence,sourceFlux_real_projection g w u hu,
    coordPartial_real_projection _ (hf _),Complex.mul_re,← Complex.ofReal_inv]

theorem gaussianWaveField_source_residual
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (hV : ∀ a, ContDiff ℝ ∞ (V a))
    (hf : ∀ a i, ContDiff ℝ ∞ (sourceFlux g w (V a) i))
    (coeff : ι × Fin 2 → ℝ) (lam : ℝ) :
    (fun x ↦ sourceWeightedOperator g w (fun z ↦ (gaussianWaveField V coeff z:ℂ)) x +
      (lam:ℂ)*(gaussianWaveField V coeff x:ℂ)) =
    fun x ↦ (gaussianWaveField
      (fun a x ↦ sourceWeightedOperator g w (V a) x+(lam:ℂ)*V a x) coeff x:ℂ) := by
  let Z : ι → _root_.OAI.Yau.Jets.Coord → ℂ := fun a x ↦ gaussianCoefficient coeff a*V a x
  have hZ (a : ι) : ContDiff ℝ ∞ (Z a) := contDiff_const.mul (hV a)
  have hZf (a : ι) (i : Fin 4) : ContDiff ℝ ∞ (sourceFlux g w (Z a) i) := by
    dsimp only [Z]
    rw [sourceFlux_const_mul g w _ (hV a)]
    exact contDiff_const.mul (hf a i)
  have hsum : ContDiff ℝ ∞ (fun x ↦ ∑ a, Z a x) := ContDiff.sum (fun a _ ↦ hZ a)
  have hsumf (i : Fin 4) : ContDiff ℝ ∞ (sourceFlux g w (fun x ↦ ∑ a, Z a x) i) := by
    rw [sourceFlux_finite_sum g w Z (fun a ↦ (hZ a).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
    exact ContDiff.sum (fun a _ ↦ hZf a i)
  change (fun x ↦ sourceWeightedOperator g w (fun z ↦ (((∑ a, Z a z).re):ℂ)) x +
      (lam:ℂ)*(((∑ a, Z a x).re):ℂ)) = _
  rw [sourceWeightedOperator_real_projection g w _ (hsum.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun i ↦ (hsumf i).differentiable (by simp)),
    sourceWeightedOperator_finite_sum g w Z (fun a ↦ (hZ a).differentiable (by simp))
      (fun a i ↦ (hZf a i).differentiable (by simp))]
  funext x
  simp only [Z,sourceWeightedOperator_const_mul g w _ (hV _) (hf _),gaussianWaveField]
  apply Complex.ext <;> simp [Complex.mul_re,Finset.mul_sum,Finset.sum_add_distrib,mul_add,
    mul_left_comm,Finset.sum_sub_distrib,mul_sub]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSourceOperator
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

lemma smoothFluxOperator_smooth (v : _root_.OAI.Yau.Jets.Coord → ℂ) (F : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hv : ContDiff ℝ ∞ v) (hF : ∀ i j, ContDiff ℝ ∞ (F i j))
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (smoothFluxOperator v F u) :=
  hv.mul (ContDiff.sum (fun i _ ↦ coordPartial_contDiff
    (ContDiff.sum (fun j _ ↦ (hF i j).mul (coordPartial_contDiff hu j))) i))

theorem compact_source_operator_coefficients {Q U : Set _root_.OAI.Yau.Jets.Coord}
    (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x) :
    ∃ (v : _root_.OAI.Yau.Jets.Coord → ℂ) (F : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ),
      ContDiff ℝ ∞ v ∧ (∀ i j, ContDiff ℝ ∞ (F i j)) ∧
      ∀ x ∈ Q, ∀ u : _root_.OAI.Yau.Jets.Coord → ℂ,
        sourceWeightedOperator g w u =ᶠ[𝓝 x] smoothFluxOperator v F u := by
  obtain ⟨G,W,A,E,hG,hW,_,hGs,hGp,hE,hQE,hEU,hWp,he⟩ :=
    compact_source_representatives hQ hU hQU hUn g hg hs hp w (fun _ ↦ 0) hw contDiffOn_const hwp
  have hWi : ContDiffOn ℝ ∞ (fun x ↦ (W x)⁻¹) E :=
    hW.contDiffOn.inv (fun x hx ↦ ne_of_gt (hWp x hx))
  obtain ⟨V,hV,_,_,hVe⟩ := compact_smooth_extension hQ hE hQE _ hWi
  let F : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ := fun i j x ↦ (W x:ℂ)*(sourcePrincipal G i j x:ℂ)
  have hF (i j : Fin 4) : ContDiff ℝ ∞ (F i j) := by
    have ha : ContDiff ℝ ∞ (sourcePrincipal G i j) :=
      contDiff_iff_contDiffAt.mpr (fun x ↦ sourcePrincipal_smooth_at G hG x (hGp x) i j)
    exact (Complex.ofRealCLM.contDiff.comp hW).mul (Complex.ofRealCLM.contDiff.comp ha)
  refine ⟨fun x ↦ (V x:ℂ),F,Complex.ofRealCLM.contDiff.comp hV,hF,?_⟩
  intro x hx u
  have hcoef := sourceOperator_coefficients_eventuallyEq (he x (hQE hx)).1.symm
    (he x (hQE hx)).2.1.symm u
  filter_upwards [hcoef,hVe x hx] with z hz hvz
  rw [hz]
  simp only [smoothFluxOperator,sourceWeightedOperator,complexDivergence,F,hvz,
    Complex.ofReal_inv]
  rfl

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_OperatorAddition
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

lemma coordPartial_add (u v : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (i : Fin 4) :
    _root_.OAI.Yau.Jets.coordPartial i (fun z ↦ u z+v z) = fun z ↦ _root_.OAI.Yau.Jets.coordPartial i u z+_root_.OAI.Yau.Jets.coordPartial i v z := by
  funext x
  simp [_root_.OAI.Yau.Jets.coordPartial,fderiv_fun_add (hu x) (hv x)]

lemma smoothFluxOperator_add (v : _root_.OAI.Yau.Jets.Coord → ℂ) (F : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hF : ∀ i j, ContDiff ℝ ∞ (F i j))
    (u t : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t) :
    smoothFluxOperator v F (fun z ↦ u z+t z) =
      fun z ↦ smoothFluxOperator v F u z+smoothFluxOperator v F t z := by
  have he (i : Fin 4) :
      (fun z ↦ ∑ j, F i j z*_root_.OAI.Yau.Jets.coordPartial j (fun z ↦ u z+t z) z) =
      (fun z ↦ (∑ j, F i j z*_root_.OAI.Yau.Jets.coordPartial j u z)+(∑ j, F i j z*_root_.OAI.Yau.Jets.coordPartial j t z)) := by
    funext z
    simp [coordPartial_add u t (hu.differentiable (by simp)) (ht.differentiable (by simp)),
      mul_add,Finset.sum_add_distrib]
  have hfu (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ ∑ j, F i j z*_root_.OAI.Yau.Jets.coordPartial j u z) :=
    ContDiff.sum (fun j _ ↦ (hF i j).mul (coordPartial_contDiff hu j))
  have hft (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ ∑ j, F i j z*_root_.OAI.Yau.Jets.coordPartial j t z) :=
    ContDiff.sum (fun j _ ↦ (hF i j).mul (coordPartial_contDiff ht j))
  funext x
  simp only [smoothFluxOperator,he,
    coordPartial_add _ _ ((hfu _).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ((hft _).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    Finset.sum_add_distrib,mul_add]

lemma sourceOperator_add_germ {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (u t : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t)
    {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ U) :
    sourceWeightedOperator g w (fun z ↦ u z+t z) =ᶠ[𝓝 x]
      (fun z ↦ sourceWeightedOperator g w u z+sourceWeightedOperator g w t z) := by
  obtain ⟨v,F,hv,hF,he⟩ := compact_source_operator_coefficients (isCompact_singleton (x := x))
    hU (singleton_subset_iff.mpr hx) ⟨x,hx⟩ g hg hs hp w hw hwp
  filter_upwards [he x (mem_singleton x) u,he x (mem_singleton x) t,
    he x (mem_singleton x) (fun z ↦ u z+t z)] with z hzu hzt hzsum
  rw [hzsum,smoothFluxOperator_add v F hF u t hu ht]
  exact congrArg₂ (· + ·) hzu.symm hzt.symm

lemma sourceOperator_smoothAt {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (sourceWeightedOperator g w u) x := by
  obtain ⟨v,F,hv,hF,he⟩ := compact_source_operator_coefficients (isCompact_singleton (x := x))
    hU (singleton_subset_iff.mpr hx) ⟨x,hx⟩ g hg hs hp w hw hwp
  exact (smoothFluxOperator_smooth v F hv hF u hu).contDiffAt.congr_of_eventuallyEq
    (he x (mem_singleton x) u)

theorem sourceOperator_add_supported {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (u t : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t)
    (hsub : tsupport t ⊆ U) :
    sourceWeightedOperator g w (fun z ↦ u z+t z) =
      fun z ↦ sourceWeightedOperator g w u z+sourceWeightedOperator g w t z := by
  funext x
  by_cases hx : x ∈ U
  · exact (sourceOperator_add_germ hU g hg hs hp w hw hwp u t hu ht hx).self_of_nhds
  · have hz : t =ᶠ[𝓝 x] (fun _ ↦ 0) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hsub h))
    have hsum : (fun z ↦ u z+t z) =ᶠ[𝓝 x] u := by
      filter_upwards [hz] with z hz
      simp [hz]
    rw [(sourceOperator_eventuallyEq g w hsum).self_of_nhds,
      (sourceOperator_eventuallyEq g w hz).self_of_nhds,sourceWeightedOperator_zero]
    simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FiniteWaveSupport
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
variable {ι : Type*} [Fintype ι]

lemma gaussianWaveField_tsupport_subset (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (a : ι × Fin 2 → ℝ)
    {C : Set _root_.OAI.Yau.Jets.Coord} (hC : IsClosed C) (hV : ∀ i, tsupport (V i) ⊆ C) :
    tsupport (gaussianWaveField V a) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  by_contra hxc
  apply hx
  have hz (i : ι) : V i x = 0 := image_eq_zero_of_notMem_tsupport (fun hi ↦ hxc (hV i hi))
  simp [gaussianWaveField,hz]

lemma complexified_tsupport_subset (u : _root_.OAI.Yau.Jets.Coord → ℝ) {C : Set _root_.OAI.Yau.Jets.Coord} (hC : IsClosed C)
    (hu : tsupport u ⊆ C) : tsupport (fun x ↦ (u x : ℂ)) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  apply hu
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz])

lemma source_residual_tsupport_subset
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (lam : ℂ) {C : Set _root_.OAI.Yau.Jets.Coord} (hC : IsClosed C) (hu : tsupport u ⊆ C) :
    tsupport (fun x ↦ sourceWeightedOperator g w u x + lam*u x) ⊆ C := by
  apply closure_minimal _ hC
  intro x hx
  by_contra hxc
  have hz : x ∉ tsupport u := fun h ↦ hxc (hu h)
  have he : u =ᶠ[𝓝 x] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hz
  have hop := (sourceOperator_eventuallyEq g w he).eq_of_nhds
  apply hx
  simp only [hop,sourceWeightedOperator_zero,Pi.zero_apply,he.eq_of_nhds,mul_zero,add_zero]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SeededResidual
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

lemma realSourceResidual_smoothAt {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (lam : ℝ) (u : _root_.OAI.Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (realSourceResidual g w lam u) x :=
  (sourceOperator_smoothAt hU g hg hs hp w hw hwp _ (Complex.ofRealCLM.contDiff.comp hu) hx).add
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.comp hu).contDiffAt)

lemma realSourceResidual_add_supported {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (lam : ℝ) (u t : _root_.OAI.Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t)
    (hsub : tsupport t ⊆ U) :
    realSourceResidual g w lam (fun z ↦ u z+t z) =
      fun z ↦ realSourceResidual g w lam u z+realSourceResidual g w lam t z := by
  have hsub' : tsupport (fun z ↦ (t z:ℂ)) ⊆ U := by
    have he : Function.support (fun z ↦ (t z:ℂ)) = Function.support t := by
      ext z
      simp [Function.mem_support]
    simpa only [tsupport,he] using hsub
  have he := sourceOperator_add_supported hU g hg hs hp w hw hwp
    (fun z ↦ (u z:ℂ)) (fun z ↦ (t z:ℂ))
    (Complex.ofRealCLM.contDiff.comp hu) (Complex.ofRealCLM.contDiff.comp ht) hsub'
  funext x
  simp only [realSourceResidual,Complex.ofReal_add,he]
  ring

lemma derivativeBound_add_at {k : ℕ} {f g : _root_.OAI.Yau.Jets.Coord → ℂ} {x : _root_.OAI.Yau.Jets.Coord} {A B : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (ha : DerivativeBound k f x A) (hb : DerivativeBound k g x B) :
    DerivativeBound k (fun z ↦ f z+g z) x (A+B) := by
  intro j hj
  change ‖iteratedFDeriv ℝ j (f+g) x‖ ≤ A+B
  rw [iteratedFDeriv_add_apply
    (hf.of_le (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top)))
    (hg.of_le (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top)))]
  exact (norm_add_le _ _).trans (add_le_add (ha j hj) (hb j hj))

theorem realSourceResidual_add_bound {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (lam : ℝ) (u t : _root_.OAI.Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t)
    (hsub : tsupport t ⊆ U) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ U) (k : ℕ) (B C : ℝ)
    (hb : DerivativeBound k (realSourceResidual g w lam u) x B)
    (hc : DerivativeBound k (realSourceResidual g w lam t) x C) :
    DerivativeBound k (realSourceResidual g w lam (fun z ↦ u z+t z)) x (B+C) := by
  rw [realSourceResidual_add_supported hU g hg hs hp w hw hwp lam u t hu ht hsub]
  exact derivativeBound_add_at (realSourceResidual_smoothAt hU g hg hs hp w hw hwp lam u hu hx)
    (realSourceResidual_smoothAt hU g hg hs hp w hw hwp lam t ht hx) hb hc

end
end Yau.Geometry

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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_1_r8b039c_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_FiniteResidualBound
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

lemma complexified_iterated_norm_le (u : _root_.OAI.Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u)
    (k : ℕ) (x : _root_.OAI.Yau.Jets.Coord) :
    ‖iteratedFDeriv ℝ k (fun z ↦ (u z:ℂ)) x‖ ≤ ‖iteratedFDeriv ℝ k u x‖ := by
  have he := Complex.ofRealCLM.iteratedFDeriv_comp_left (hu.contDiffAt (x := x))
    (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))
  change iteratedFDeriv ℝ k (fun z ↦ (u z:ℂ)) x = _ at he
  rw [he]
  have hc : ‖Complex.ofRealCLM‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun z ↦ by simp)
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right hc (norm_nonneg (iteratedFDeriv ℝ k u x)))

theorem gaussianWaveField_source_residual_bound
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (hV : ∀ a, ContDiff ℝ ∞ (V a))
    (hf : ∀ a i, ContDiff ℝ ∞ (sourceFlux g w (V a) i))
    (lam : ℝ)
    (hr : ∀ a, ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w (V a) x+(lam:ℂ)*V a x))
    (coeff : ι × Fin 2 → ℝ) {R : ℝ} (hR : 0 ≤ R) (hc : coeff ∈ coefficientEvent R)
    (k : ℕ) (x : _root_.OAI.Yau.Jets.Coord) {B : ℝ}
    (hb : ∀ a, ‖iteratedFDeriv ℝ k
      (fun x ↦ sourceWeightedOperator g w (V a) x+(lam:ℂ)*V a x) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun x ↦
      sourceWeightedOperator g w (fun z ↦ (gaussianWaveField V coeff z:ℂ)) x+
      (lam:ℂ)*(gaussianWaveField V coeff x:ℂ)) x‖ ≤ (Fintype.card ι:ℝ)*R*B := by
  rw [gaussianWaveField_source_residual g w V hV hf coeff lam]
  exact (complexified_iterated_norm_le _ (gaussianWaveField_contDiff _ coeff hr) k x).trans
    (gaussianWaveField_iterated_bound _ coeff hr k x hR hc hb)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedDerivativeBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem oscillatorySeed_derivative_bound (S T : Coord → ℝ)
    (hS : ContDiff ℝ ∞ S) (hT : ContDiff ℝ ∞ T) {Q : Set Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ C > 0, ∀ N : ℝ, 1 ≤ N → ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ k (oscillatorySeed S T N) x‖ ≤ C*N^k*Real.exp (N*S x) := by
  let phi : Coord → ℂ := fun x ↦ (S x:ℂ)+Complex.I*(T x:ℂ)
  have hp : ContDiff ℝ ∞ phi :=
    (Complex.ofRealCLM.contDiff.comp hS).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hT))
  have hb (j : Fin (k+1)) : ∃ C > 0, ∀ x ∈ Q, ‖iteratedFDeriv ℝ j.val phi x‖ ≤ C := by
    obtain ⟨C,hC,hb⟩ := (hQ.image (hp.continuous_iteratedFDeriv
      (by exact_mod_cast (show (j.val:ℕ∞) ≤ ⊤ from le_top)))).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx ↦ hb _ ⟨x,hx,rfl⟩⟩
  choose b hb hbound using hb
  let D : ℝ := 1+∑ j, b j
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ ↦ (hb j).le))
  refine ⟨(k.factorial:ℝ)*D^k,by positivity,?_⟩
  intro N hN x hx
  have hphi : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i phi x‖ ≤ D := by
    intro i _ hi
    have h := (hbound ⟨i,by omega⟩ x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _))
    dsimp [D]
    linarith
  have he : oscillatorySeed S T N = fun z ↦ (waveExp phi N z).re := by
    funext z
    simp [oscillatorySeed,waveExp,Complex.exp_re,phi]
  rw [he]
  have hw : ContDiff ℝ ∞ (waveExp phi N) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp (contDiff_const.mul hp)
  have h := (realPart_iterated_norm_le (waveExp phi N) x hw.contDiffAt k).trans
    (waveExp_derivative_bound hp k x hD hN hphi)
  simpa [phi] using h

end
end Yau.Jets

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

theorem seedCoordinateField_derivative_bound {Q : Set _root_.OAI.Yau.Jets.Coord}
    (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch) (k : ℕ) :
    ∃ C > 0, ∀ N : ℕ, 0 < N → ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ k (seedCoordinateField N) x‖ ≤
        C*(N:ℝ)^k*Real.exp ((N:ℝ)*seedCoordReal x) := by
  obtain ⟨S0,T0,hS,hT,_,_,_,_,he⟩ := seed_log_compact_extensions hQ hQB
  obtain ⟨C,hC,hbound⟩ := oscillatorySeed_derivative_bound S0 T0 hS hT hQ k
  refine ⟨C,hC,?_⟩
  intro N hN x hx
  have hlog := seedCoordinateField_log_germ N (hQB hx) S0 T0 (he x hx).1 (he x hx).2
  rw [(hlog.iteratedFDeriv ℝ k).eq_of_nhds]
  simpa only [(he x hx).1.eq_of_nhds] using hbound (N:ℝ) (by exact_mod_cast hN) x hx

theorem seedCoordinateField_derivativeBound {Q : Set _root_.OAI.Yau.Jets.Coord}
    (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch) (k : ℕ) :
    ∃ C > 0, ∀ N : ℕ, 0 < N → ∀ x ∈ Q,
      DerivativeBound k (fun z ↦ (seedCoordinateField N z:ℂ)) x
        (C*(N:ℝ)^k*Real.exp ((N:ℝ)*seedCoordReal x)) := by
  have hb (j : Fin (k+1)) := seedCoordinateField_derivative_bound hQ hQB j.val
  choose b hb hbound using hb
  let C : ℝ := ∑ j, b j
  have hC : 0 < C := (hb ⟨0,by omega⟩).trans_le
    (Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _))
  refine ⟨C,hC,?_⟩
  intro N hN x hx j hj
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hbj : b ⟨j,by omega⟩ ≤ C :=
    Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _)
  exact (complexified_iterated_norm_le _ (seedCoordinateField_smooth N) j x).trans
    ((hbound ⟨j,by omega⟩ N hN x hx).trans (by gcongr))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FixedChartSeedSupport
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Set Filter Yau.Geometry Yau.Jets
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section

lemma iteratedFDeriv_zero_off_tsupport {f : _root_.OAI.Yau.Jets.Coord → ℂ} {K : Set _root_.OAI.Yau.Jets.Coord}
    (hf : tsupport f ⊆ K) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∉ K) (k : ℕ) :
    iteratedFDeriv ℝ k f x = 0 := by
  have he : f =ᶠ[𝓝 x] (fun _ ↦ 0) :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hf h))
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  simp

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_LocalResidualRegularity
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
  {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

lemma sourceFlux_zero
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ) (i : Fin 4) :
    sourceFlux g w (fun _ ↦ 0) i = 0 := by
  funext x
  simp [sourceFlux,_root_.OAI.Yau.Jets.coordPartial]

lemma sourceFlux_eventuallyEq
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    {u v : _root_.OAI.Yau.Jets.Coord → ℂ} {x : _root_.OAI.Yau.Jets.Coord} (he : u =ᶠ[𝓝 x] v) (i : Fin 4) :
    sourceFlux g w u i =ᶠ[𝓝 x] sourceFlux g w v i := by
  filter_upwards [Filter.eventually_all.mpr (fun j ↦ coordPartial_eventuallyEq he j)] with z hz
  simp only [sourceFlux,hz]

lemma LocalCompactWaveData.supported_flux_smooth
    (a : LocalCompactWaveData g w S D m J K k0)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hs : tsupport u ⊆ a.E) (i : Fin 4) :
    ContDiff ℝ ∞ (sourceFlux g w u i) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport u
  · obtain ⟨hg,hw,_⟩ := a.germ x (hs hx)
    apply (sourceFlux_smooth_at a.G a.smooth_G a.W a.smooth_W u hu x
      (a.positive_G x) i).congr_of_eventuallyEq
    filter_upwards [hg,hw] with z hz hwz
    simp only [sourceFlux,sourcePrincipal,hz,hwz]
  · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have hz : u =ᶠ[𝓝 x] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hx
    have he := sourceFlux_eventuallyEq g w hz i
    filter_upwards [he] with z hz
    simpa only [sourceFlux_zero,Pi.zero_apply] using hz

lemma LocalCompactWaveData.supported_residual_smooth
    (a : LocalCompactWaveData g w S D m J K k0)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hs : tsupport u ⊆ a.E)
    (hw : ∀ x ∈ tsupport u, w x ≠ 0) (lam : ℂ) :
    ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w u x+lam*u x) := by
  have hf (i : Fin 4) := a.supported_flux_smooth u hu hs i
  have hd : ContDiff ℝ ∞ (complexDivergence (sourceFlux g w u)) :=
    ContDiff.sum (fun i _ ↦ coordPartial_contDiff (hf i) i)
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport u
  · have hwe := (a.germ x (hs hx)).2.1
    have hws : ContDiffAt ℝ ∞ w x := a.smooth_W.contDiffAt.congr_of_eventuallyEq hwe.symm
    exact (((Complex.ofRealCLM.contDiff.contDiffAt.comp x hws).inv
      (Complex.ofReal_ne_zero.mpr (hw x hx))).mul hd.contDiffAt).add
        (contDiffAt_const.mul hu.contDiffAt)
  · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have he : u =ᶠ[𝓝 x] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hx
    filter_upwards [he,sourceOperator_eventuallyEq g w he] with z hz ho
    simp only [ho,hz,sourceWeightedOperator_zero,Pi.zero_apply,mul_zero,add_zero]

theorem LocalCompactWaveData.wave_residual_regular
    (a : LocalCompactWaveData g w S D m J K k0) (hw : ∀ x ∈ a.E, w x ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∀ t : a.cover.Parameter × Fin 3,
      (∀ i, ContDiff ℝ ∞ (sourceFlux g w (a.beams.wave (n:ℝ) t) i)) ∧
      ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w (a.beams.wave (n:ℝ) t) x+
        ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*a.beams.wave (n:ℝ) t x) := by
  filter_upwards [a.estimates] with n hn
  intro t
  have ht := hn t
  exact ⟨a.supported_flux_smooth _ ht.1 ht.2.2.1,
    a.supported_residual_smooth _ ht.1 ht.2.2.1 (fun x hx ↦ hw x (ht.2.2.1 hx)) _⟩

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma lattice_scale_eq_inv_sqrt (n : ℕ) : (n:ℝ)^(-1/2:ℝ) = (Real.sqrt n)⁻¹ := by
  rw [show (-1/2:ℝ) = -(1/2) by ring,Real.rpow_neg,Real.sqrt_eq_rpow]
  positivity

theorem source_grid_card_bound {U : Set _root_.OAI.Yau.Jets.Coord} (hU : Bornology.IsBounded U) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → (Nat.card (SourceGrid U n) : ℝ) ≤ C*(n:ℝ)^2 := by
  obtain ⟨B,hB,hbound⟩ := hU.exists_pos_norm_le
  refine ⟨(2*B+3)^4,by positivity,?_⟩
  intro n hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
  have hs2 : (Real.sqrt n)^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
  let M : ℤ := ⌈B*Real.sqrt n⌉
  have hM0 : 0 ≤ M := Int.ceil_nonneg (by positivity)
  have hMc : (M:ℝ) < B*Real.sqrt n+1 := Int.ceil_lt_add_one _
  have hcoords (z : SourceGrid U n) (i : Fin 4) : z.val i ∈ Icc (-M) M := by
    have hi := (norm_le_pi_norm (scaledLatticePoint n z) i).trans (hbound _ z.property)
    change |(n:ℝ)^(-1/2:ℝ)*(z.val i:ℝ)| ≤ B at hi
    rw [lattice_scale_eq_inv_sqrt,abs_mul,abs_of_pos (inv_pos.mpr hs)] at hi
    have hmul := mul_le_mul_of_nonneg_left hi hs.le
    have hcancel : Real.sqrt n * ((Real.sqrt n)⁻¹ * |(z.val i:ℝ)|) = |(z.val i:ℝ)| := by
      field_simp
    rw [hcancel] at hmul
    have ha : |(z.val i:ℝ)| ≤ (M:ℝ) := hmul.trans (by simpa [mul_comm] using Int.le_ceil (B*Real.sqrt n))
    have hp := abs_le.mp ha
    exact ⟨by exact_mod_cast hp.1,by exact_mod_cast hp.2⟩
  let f : SourceGrid U n → (Fin 4 → Icc (-M) M) := fun z i ↦ ⟨z.val i,hcoords z i⟩
  have hfi : Function.Injective f := by
    intro z w h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have hc := Nat.card_le_card_of_injective f hfi
  have hbox : Nat.card (Fin 4 → Icc (-M) M) = ((2*M+1).toNat)^4 := by
    rw [Nat.card_fun]
    simp [Nat.card_eq_fintype_card,Int.card_Icc,show M+1- -M = 2*M+1 by ring]
  rw [hbox] at hc
  have hcR : (Nat.card (SourceGrid U n):ℝ) ≤ ((2*M+1).toNat:ℝ)^4 := by exact_mod_cast hc
  have hcast : ((2*M+1).toNat:ℝ) = 2*(M:ℝ)+1 := by
    have hi : ((2*M+1).toNat:ℤ) = 2*M+1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hi
  rw [hcast] at hcR
  have hmnon : (0:ℝ) ≤ 2*(M:ℝ)+1 := by exact_mod_cast (show (0:ℤ) ≤ 2*M+1 by omega)
  have hmle : 2*(M:ℝ)+1 ≤ (2*B+3)*Real.sqrt n := by nlinarith
  have hpow := pow_le_pow_left₀ hmnon hmle 4
  calc
    _ ≤ (2*(M:ℝ)+1)^4 := hcR
    _ ≤ ((2*B+3)*Real.sqrt n)^4 := hpow
    _ = (2*B+3)^4*(n:ℝ)^2 := by
      rw [mul_pow,show (Real.sqrt n)^4 = ((Real.sqrt n)^2)^2 by ring,hs2]

theorem source_coefficient_card_bound {U : Set _root_.OAI.Yau.Jets.Coord} (hU : Bornology.IsBounded U) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → (Nat.card (SourceGrid U n × Fin 3):ℝ) ≤ C*(n:ℝ)^2 := by
  obtain ⟨C,hC,hb⟩ := source_grid_card_bound hU
  refine ⟨3*C,by positivity,?_⟩
  intro n hn
  have h := hb n hn
  rw [Nat.card_prod]
  norm_num
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_LatticeResidualBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
  {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

theorem LocalCompactWaveData.lattice_residual_derivative_bound
    (a : LocalCompactWaveData g w S D m J K k0)
    (hw : ∀ x ∈ a.E, w x ≠ 0) (hUD : U ⊆ D) (hUb : Bornology.IsBounded U) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        let u := gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff
        let residual := fun x ↦ sourceWeightedOperator g w (fun z ↦ (u z:ℂ)) x+
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u x:ℂ)
        ContDiff ℝ ∞ residual ∧ ∀ x : _root_.OAI.Yau.Jets.Coord,
          DerivativeBound k0 residual x (C*(n:ℝ)^(3-(K:ℝ))*Real.exp ((n:ℝ)*S x)) := by
  obtain ⟨C,hC,hcard⟩ := source_coefficient_card_bound hUb
  have hCr := a.beams.Cr_pos
  refine ⟨C*a.beams.Cr,mul_pos hC a.beams.Cr_pos,?_⟩
  filter_upwards [a.estimates,a.wave_residual_regular hw,eventually_gt_atTop (0:ℕ)]
    with n hn hreg hnpos
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  let := hfin
  refine ⟨hfin,?_⟩
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  let lam : ℝ := 4*(n:ℝ)^2+6*(n:ℝ)
  have hlam : (lam:ℂ) = (4:ℂ)*(n:ℂ)^2+6*(n:ℂ) := by dsimp [lam]; push_cast; rfl
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hn (latticeFrame a.cover hUD n i.1,i.2)).1
  have hf (i : SourceGrid U n × Fin 3) (j : Fin 4) :
      ContDiff ℝ ∞ (sourceFlux g w (V i) j) :=
    (hreg (latticeFrame a.cover hUD n i.1,i.2)).1 j
  have hr (i : SourceGrid U n × Fin 3) :
      ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w (V i) x+(lam:ℂ)*V i x) := by
    rw [hlam]
    exact (hreg (latticeFrame a.cover hUD n i.1,i.2)).2
  intro coeff hc
  change ContDiff ℝ ∞ (fun x ↦ sourceWeightedOperator g w
      (fun z ↦ (gaussianWaveField V coeff z:ℂ)) x+_*(gaussianWaveField V coeff x:ℂ)) ∧ _
  constructor
  · rw [← hlam,gaussianWaveField_source_residual g w V hV hf coeff lam]
    exact Complex.ofRealCLM.contDiff.comp (gaussianWaveField_contDiff _ coeff hr)
  · intro x k hk
    have hb (i : SourceGrid U n × Fin 3) :
        ‖iteratedFDeriv ℝ k (fun x ↦ sourceWeightedOperator g w (V i) x+(lam:ℂ)*V i x) x‖ ≤
          a.beams.Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x) := by
      rw [hlam]
      exact ((hn (latticeFrame a.cover hUD n i.1,i.2)).2.2.2.2 x).2 k hk
    have hh := gaussianWaveField_source_residual_bound g w V hV hf lam hr coeff
      hnR.le hc k x hb
    rw [hlam] at hh
    refine hh.trans ?_
    have hcardR : (Fintype.card (SourceGrid U n × Fin 3):ℝ) ≤ C*(n:ℝ)^2 := by
      simpa only [Nat.card_eq_fintype_card] using hcard n hnpos
    calc
      _ ≤ (C*(n:ℝ)^2)*(n:ℝ)*(a.beams.Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x)) := by
        gcongr
      _ = (C*a.beams.Cr)*((n:ℝ)^3*(n:ℝ)^(-(K:ℝ)))*Real.exp ((n:ℝ)*S x) := by ring
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_add hnR]; rfl

theorem LocalCompactWaveData.lattice_residual_accuracy
    (K' : ℕ) (a : LocalCompactWaveData g w S D m J (K'+3) k0)
    (hw : ∀ x ∈ a.E, w x ≠ 0) (hUD : U ⊆ D) (hUb : Bornology.IsBounded U) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        let u := gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff
        let residual := fun x ↦ sourceWeightedOperator g w (fun z ↦ (u z:ℂ)) x+
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u x:ℂ)
        ContDiff ℝ ∞ residual ∧ ∀ x : _root_.OAI.Yau.Jets.Coord,
          DerivativeBound k0 residual x (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*S x)) := by
  have he : (3:ℝ)-((K'+3:ℕ):ℝ) = -(K':ℝ) := by push_cast <;> ring
  simpa only [he] using a.lattice_residual_derivative_bound hw hUD hUb

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LocalWaveSupportCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped Topology
noncomputable section

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
  {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

theorem LocalCompactWaveData.uniform_support_core (a : LocalCompactWaveData g w S D m J K k0)
    (hD : IsCompact D) {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ C : Set _root_.OAI.Yau.Jets.Coord, IsCompact C ∧ C ⊆ Ω ∧ D ⊆ interior C ∧
      ∀ᶠ n : ℕ in atTop, ∀ t : a.cover.Parameter × Fin 3,
        tsupport (a.beams.wave (n:ℝ) t) ⊆ C ∧
        ∀ x ∉ C, ∀ k : ℕ,
          iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w (a.beams.wave (n:ℝ) t) z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*a.beams.wave (n:ℝ) t z) x = 0 := by
  obtain ⟨C,hC,hDC,hCΩ⟩ := exists_compact_between hD hΩ hDΩ
  obtain ⟨ε,hε,hth⟩ := hD.exists_cthickening_subset_open isOpen_interior hDC
  have hsmall : ∀ᶠ n : ℕ in atTop, a.beams.R*(n:ℝ)^(-1/3:ℝ) < ε := by
    apply eventually_nat_frequency (P := fun N : ℝ ↦ a.beams.R*N^(-1/3:ℝ) < ε)
    have ht : Tendsto (fun N : ℝ ↦ a.beams.R*N^(-1/3:ℝ)) atTop (𝓝 0) := by
      simpa only [neg_div,mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul a.beams.R
    exact ht.eventually (gt_mem_nhds hε)
  refine ⟨C,hC,hCΩ,hDC,?_⟩
  filter_upwards [a.estimates,hsmall] with n hn hnε
  intro t
  have hsup : tsupport (a.beams.wave (n:ℝ) t) ⊆ C := by
    intro x hx
    have hb := (norm_le_sourceEuclideanNorm (x-coverSourceCenter a.cover t.1)).trans
      ((hn t).2.2.2.1 hx)
    have hc : coverSourceCenter a.cover t.1 ∈ D := (a.cover.center t.1).property
    apply interior_subset (hth (mem_cthickening_of_dist_le x (coverSourceCenter a.cover t.1) ε D hc ?_))
    rw [dist_eq_norm]
    exact (hb.trans_lt hnε).le
  refine ⟨hsup,?_⟩
  intro x hx k
  exact source_residual_derivative_zero g w _ _ x (fun hz ↦ hx (hsup hz)) k

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_LatticeResidualSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
  {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

theorem LocalCompactWaveData.lattice_residual_support
    (a : LocalCompactWaveData g w S D m J K k0)
    (hD : IsCompact D) (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsOpen Ω) (hDΩ : D ⊆ Ω) :
    ∃ C : Set _root_.OAI.Yau.Jets.Coord, IsCompact C ∧ C ⊆ Ω ∧ D ⊆ interior C ∧
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
        letI := hfin
        ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
          let u := gaussianWaveField
            (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff
          tsupport u ⊆ C ∧
          tsupport (fun z ↦ sourceWeightedOperator g w (fun x ↦ (u x : ℂ)) z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u z:ℂ)) ⊆ C ∧
          ∀ x ∉ C, ∀ k : ℕ,
            iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w (fun x ↦ (u x:ℂ)) z +
              ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u z:ℂ)) x = 0 := by
  obtain ⟨C,hC,hCΩ,hDC,hcore⟩ := a.uniform_support_core hD hΩ hDΩ
  refine ⟨C,hC,hCΩ,hDC,?_⟩
  filter_upwards [hcore,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hVs (i : SourceGrid U n × Fin 3) : tsupport (V i) ⊆ C :=
    (hn (latticeFrame a.cover hUD n i.1,i.2)).1
  have hu := gaussianWaveField_tsupport_subset V coeff hC.isClosed hVs
  have hc := complexified_tsupport_subset (gaussianWaveField V coeff) hC.isClosed hu
  refine ⟨hu,source_residual_tsupport_subset g w _ _ hC.isClosed hc,?_⟩
  intro x hx k
  exact source_residual_derivative_zero g w _ _ x (fun hz ↦ hx (hc hz)) k

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_PlacedEnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma PlacedEnvelopeData.closure_U_branch {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    closure d.U ⊆ seedCoordBranch :=
  d.closure_U_Ω.trans (subset_closure.trans (d.closure_Ω_patch.trans
    (subset_closure.trans (d.patch_V.trans d.V_branch))))

lemma PlacedEnvelopeData.closure_U_V {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) :
    closure d.U ⊆ d.V :=
  d.closure_U_Ω.trans (subset_closure.trans (d.closure_Ω_patch.trans
    (subset_closure.trans d.patch_V)))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_PlacedRandomResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology
noncomputable section

theorem PlacedEnvelopeData.random_residual {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T) (ha : 0 ≤ a)
    (hg : ContDiffOn ℝ ∞ g seedCoordBranch)
    (hs : ∀ x ∈ seedCoordBranch, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ seedCoordBranch, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w seedCoordBranch)
    (hwp : ∀ x ∈ seedCoordBranch, 0 < w x) (k0 K' : ℕ) :
    ∃ b : LocalCompactWaveData g w d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set _root_.OAI.Yau.Jets.Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∀ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let u := gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
            let residual := fun x ↦ sourceWeightedOperator g w (fun z ↦ (u z:ℂ)) x+
              ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*(u x:ℂ)
            tsupport u ⊆ Q ∧ tsupport residual ⊆ Q ∧
            (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k residual x = 0) ∧
            (coeff ∈ coefficientEvent (n:ℝ) → ContDiff ℝ ∞ residual ∧
              ∀ x : _root_.OAI.Yau.Jets.Coord, DerivativeBound k0 residual x
                (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) := by
  obtain ⟨b,hb⟩ := d.waves_in_domain ha hg hs hp w hw hwp k0 (K'+3)
  have hUb : Bornology.IsBounded d.U := d.compact_closure_U.isBounded.subset subset_closure
  have hbwp : ∀ x ∈ b.E, w x ≠ 0 := fun x hx ↦ ne_of_gt (hwp x (d.V_branch (hb hx)))
  obtain ⟨C,hC,hbound⟩ := b.lattice_residual_accuracy K' hbwp subset_closure hUb
  obtain ⟨Q,hQ,hQΩ,hUQ,hsupport⟩ := b.lattice_residual_support d.compact_closure_U
    subset_closure hUb d.open_Ω d.closure_U_Ω
  refine ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,?_⟩
  filter_upwards [hbound,hsupport] with n hn hsupp
  obtain ⟨hfin,hn⟩ := hn
  obtain ⟨hfin',hsupp⟩ := hsupp
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff
  exact ⟨(hsupp coeff).1,(hsupp coeff).2.1,(hsupp coeff).2.2,hn coeff⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_CompactOperatorBounds
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

lemma compact_finite_derivativeBound {ι : Type*} [Fintype ι]
    (f : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ C > 0, ∀ i x, x ∈ Q → DerivativeBound k (f i) x C := by
  have hb (i : ι) (j : Fin (k+1)) : ∃ C > 0, ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ j.val (f i) x‖ ≤ C := by
    obtain ⟨C,hC,hb⟩ := (hQ.image ((hf i).continuous_iteratedFDeriv
      (by exact_mod_cast (show (j.val:ℕ∞) ≤ ⊤ from le_top)))).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx ↦ hb _ ⟨x,hx,rfl⟩⟩
  choose b hb hbound using hb
  let C : ℝ := 1+∑ i, ∑ j, b i j
  have hsum (i : ι) : 0 ≤ ∑ j, b i j := Finset.sum_nonneg (fun j _ ↦ (hb i j).le)
  have hC : 0 < C := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hsum i)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro i x hx j hj
  refine (hbound i ⟨j,by omega⟩ x hx).trans ?_
  have h1 := Finset.single_le_sum (fun j _ ↦ (hb i j).le) (Finset.mem_univ ⟨j,by omega⟩)
  have h2 := Finset.single_le_sum (fun i _ ↦ hsum i) (Finset.mem_univ i)
  dsimp [C]
  linarith

lemma smoothFluxOperator_derivativeBound
    (v : _root_.OAI.Yau.Jets.Coord → ℂ) (F : Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hv : ContDiff ℝ ∞ v) (hF : ∀ i j, ContDiff ℝ ∞ (F i j))
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : _root_.OAI.Yau.Jets.Coord) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hvb : DerivativeBound k v x A)
    (hFb : ∀ i j, DerivativeBound (k+1) (F i j) x A)
    (hub : DerivativeBound (k+2) u x B) :
    DerivativeBound k (smoothFluxOperator v F u) x
      ((2^k*A*(4*(4*(2^(k+1)*A))))*B) := by
  let flux : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ := fun i z ↦ ∑ j, F i j z*_root_.OAI.Yau.Jets.coordPartial j u z
  have hs (i : Fin 4) : ContDiff ℝ ∞ (flux i) :=
    ContDiff.sum (fun j _ ↦ (hF i j).mul (coordPartial_contDiff hu j))
  have hb (i : Fin 4) : DerivativeBound (k+1) (flux i) x (4*(2^(k+1)*A*B)) := by
    have h := DerivativeBound.sum Finset.univ
      (fun j _ ↦ (hF i j).mul (coordPartial_contDiff hu j))
      (fun j _ ↦ (hFb i j).mul (hF i j) (coordPartial_contDiff hu j) hA hB
        (hub.coordPartial hu j))
    simpa [flux] using h
  have hd : DerivativeBound k (fun z ↦ ∑ i, _root_.OAI.Yau.Jets.coordPartial i (flux i) z) x
      (4*(4*(2^(k+1)*A*B))) := by
    have h := DerivativeBound.sum Finset.univ
      (fun i _ ↦ coordPartial_contDiff (hs i) i)
      (fun i _ ↦ (hb i).coordPartial (hs i) i)
    simpa using h
  have h := hvb.mul hv (ContDiff.sum (fun i _ ↦ coordPartial_contDiff (hs i) i)) hA
    (by positivity) hd
  convert h using 1 <;> first | rfl | ring

theorem source_operator_compact_derivative_bound {Q U : Set _root_.OAI.Yau.Jets.Coord}
    (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (k : ℕ) :
    ∃ C > 0, ∀ u : _root_.OAI.Yau.Jets.Coord → ℂ, ContDiff ℝ ∞ u → ∀ x ∈ Q, ∀ B : ℝ, 0 ≤ B →
      DerivativeBound (k+2) u x B → DerivativeBound k (sourceWeightedOperator g w u) x (C*B) := by
  obtain ⟨v,F,hv,hF,he⟩ := compact_source_operator_coefficients hQ hU hQU hUn g hg hs hp w hw hwp
  let f : Option (Fin 4 × Fin 4) → _root_.OAI.Yau.Jets.Coord → ℂ := fun i ↦ match i with
    | none => v
    | some (i,j) => F i j
  have hf (i : Option (Fin 4 × Fin 4)) : ContDiff ℝ ∞ (f i) := by
    cases i with
    | none => exact hv
    | some ij => exact hF ij.1 ij.2
  obtain ⟨A,hA,hbound⟩ := compact_finite_derivativeBound f hf hQ (k+1)
  refine ⟨2^k*A*(4*(4*(2^(k+1)*A))),by positivity,?_⟩
  intro u hu x hx B hB hub j hj
  rw [((he x hx u).iteratedFDeriv ℝ j).eq_of_nhds]
  exact smoothFluxOperator_derivativeBound v F hv hF u hu k x hA.le hB
    ((hbound none x hx).mono (by omega)) (fun i j ↦ hbound (some (i,j)) x hx) hub j hj

theorem source_residual_compact_derivative_bound {Q U : Set _root_.OAI.Yau.Jets.Coord}
    (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (k : ℕ) :
    ∃ C > 0, ∀ u : _root_.OAI.Yau.Jets.Coord → ℂ, ContDiff ℝ ∞ u → ∀ x ∈ Q, ∀ B : ℝ, 0 ≤ B →
      DerivativeBound (k+2) u x B → ∀ lam : ℂ,
        DerivativeBound k (fun z ↦ sourceWeightedOperator g w u z+lam*u z) x ((C+‖lam‖)*B) := by
  obtain ⟨C,hC,hbound⟩ := source_operator_compact_derivative_bound hQ hU hQU hUn g hg hs hp w hw hwp k
  obtain ⟨v,F,hv,hF,he⟩ := compact_source_operator_coefficients hQ hU hQU hUn g hg hs hp w hw hwp
  refine ⟨C,hC,?_⟩
  intro u hu x hx B hB hub lam j hj
  have hL : ContDiffAt ℝ ∞ (sourceWeightedOperator g w u) x :=
    (smoothFluxOperator_smooth v F hv hF u hu).contDiffAt.congr_of_eventuallyEq (he x hx u)
  have hlu : ContDiff ℝ ∞ (lam • u) := contDiff_const.mul hu
  change ‖iteratedFDeriv ℝ j (sourceWeightedOperator g w u+lam • u) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hL.of_le (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top)))
    (hlu.of_le (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
    iteratedFDeriv_const_smul_apply (hu.of_le
      (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  have hh := add_le_add (hbound u hu x hx B hB hub j hj)
    (mul_le_mul_of_nonneg_left (hub j (by omega)) (norm_nonneg lam))
  simpa only [add_mul] using hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SeedResidualBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem seedCoordinateField_residual_polynomial_bound {Q U : Set _root_.OAI.Yau.Jets.Coord}
    (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch)
    (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (k : ℕ) :
    ∃ C > 0, ∀ N : ℕ, 0 < N → ∀ x ∈ Q,
      DerivativeBound k (fun z ↦ sourceWeightedOperator g w
        (fun y ↦ (seedCoordinateField N y:ℂ)) z+
          (seedEigenvalue N:ℂ)*(seedCoordinateField N z:ℂ)) x
        (C*(N:ℝ)^(k+4)*Real.exp ((N:ℝ)*seedCoordReal x)) := by
  obtain ⟨C,hC,hbound⟩ := source_residual_compact_derivative_bound hQ hU hQU hUn g hg hs hp w hw hwp k
  obtain ⟨B,hB,hseed⟩ := seedCoordinateField_derivativeBound hQ hQB (k+2)
  refine ⟨(C+10)*B,by positivity,?_⟩
  intro N hN x hx j hj
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn2 : (1:ℝ) ≤ (N:ℝ)^2 := one_le_pow₀ hn
  have hlam : ‖(seedEigenvalue N:ℂ)‖ ≤ 10*(N:ℝ)^2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (seedEigenvalue_pos hN)]
    dsimp only [seedEigenvalue]
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show (0:ℝ) ≤ N by positivity)]
  have hfactor : C+‖(seedEigenvalue N:ℂ)‖ ≤ (C+10)*(N:ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hn2 hC.le]
  have hh := hbound _ (Complex.ofRealCLM.contDiff.comp (seedCoordinateField_smooth N)) x hx
    (B*(N:ℝ)^(k+2)*Real.exp ((N:ℝ)*seedCoordReal x)) (by positivity)
    (hseed N hN x hx) (seedEigenvalue N:ℂ) j hj
  refine hh.trans ?_
  calc
    _ ≤ ((C+10)*(N:ℝ)^2)*(B*(N:ℝ)^(k+2)*Real.exp ((N:ℝ)*seedCoordReal x)) := by gcongr
    _ = _ := by rw [show k+4 = (k+2)+2 by omega,pow_add]; ring

lemma polynomial_envelope_gap {Q : Set _root_.OAI.Yau.Jets.Coord} (S S0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ x ∈ Q, S0 x+δ ≤ S x)
    (C : ℝ) (hC : 0 ≤ C) (p K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ Q,
      C*(n:ℝ)^p*Real.exp ((n:ℝ)*S0 x) ≤
        ε*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x) := by
  have ht : Tendsto (fun n : ℕ ↦ C*((n:ℝ)^(p+K)*Real.exp (-δ*(n:ℝ)))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((p+K:ℕ):ℝ) δ hδ).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop)
    simpa only [Function.comp_def,Real.rpow_natCast,mul_zero] using h.const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro x hx
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hexp : Real.exp ((n:ℝ)*S0 x) ≤ Real.exp (-δ*(n:ℝ))*Real.exp ((n:ℝ)*S x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hgap x hx) hn0.le
    nlinarith
  have hpow : (n:ℝ)^(p+K)*(n:ℝ)^(-(K:ℝ)) = (n:ℝ)^p := by
    rw [← Real.rpow_natCast,← Real.rpow_add hn0,show ((p+K:ℕ):ℝ)+ -(K:ℝ) = (p:ℝ) by push_cast; ring,
      Real.rpow_natCast]
  calc
    _ ≤ C*(n:ℝ)^p*(Real.exp (-δ*(n:ℝ))*Real.exp ((n:ℝ)*S x)) := by gcongr
    _ = (C*((n:ℝ)^(p+K)*Real.exp (-δ*(n:ℝ))))*
        ((n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x)) := by rw [← hpow]; ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hn.le
        (by positivity : 0 ≤ (n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S x))

theorem seedCoordinateField_residual_gap_bound {Q U : Set _root_.OAI.Yau.Jets.Coord}
    (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch)
    (hU : IsOpen U) (hQU : Q ⊆ U) (hUn : U.Nonempty)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ x ∈ Q, seedCoordReal x+δ ≤ S x)
    (k K' : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ Q,
      DerivativeBound k (fun z ↦ sourceWeightedOperator g w
        (fun y ↦ (seedCoordinateField N y:ℂ)) z+
          (seedEigenvalue N:ℂ)*(seedCoordinateField N z:ℂ)) x
        (ε*(N:ℝ)^(-(K':ℝ))*Real.exp ((N:ℝ)*S x)) := by
  obtain ⟨C,hC,hb⟩ := seedCoordinateField_residual_polynomial_bound hQ hQB hU hQU hUn g hg hs hp w hw hwp k
  filter_upwards [polynomial_envelope_gap S seedCoordReal hδ hgap C hC.le (k+4) K' hε,
    eventually_gt_atTop (0:ℕ)] with N hsmall hN
  intro x hx j hj
  exact (hb N hN x hx j hj).trans (hsmall x hx)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_PlacedSeedResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

theorem PlacedEnvelopeData.seed_residual {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T)
    (ha : 0 ≤ a) (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ g seedCoordBranch)
    (hs : ∀ x ∈ seedCoordBranch, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ seedCoordBranch, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w seedCoordBranch)
    (hwp : ∀ x ∈ seedCoordBranch, 0 < w x) (k K' : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ K,
      DerivativeBound k (fun z ↦ sourceWeightedOperator g w
        (fun y ↦ (seedCoordinateField N y:ℂ)) z+
          (seedEigenvalue N:ℂ)*(seedCoordinateField N z:ℂ)) x
        (ε*(N:ℝ)^(-(K':ℝ))*Real.exp ((N:ℝ)*d.S x)) := by
  have hKV : K ⊆ d.V := fun x hx ↦
    d.closure_U_V (subset_closure (d.C_U (d.inner_C (Or.inr hx))))
  have h0 : (0 : _root_.OAI.Yau.Jets.Coord) ∈ seedCoordCube a := by
    constructor <;> intro i <;> simp only [Pi.zero_apply] <;> linarith
  have h0V : (0 : _root_.OAI.Yau.Jets.Coord) ∈ d.V :=
    d.closure_U_V (subset_closure (d.C_U (d.inner_C (Or.inl h0))))
  exact seedCoordinateField_residual_gap_bound hK (hKV.trans d.V_branch)
    d.open_V hKV ⟨0,h0V⟩ g (hg.mono d.V_branch)
    (fun x hx ↦ hs x (d.V_branch hx)) (fun x hx ↦ hp x (d.V_branch hx))
    w (hw.mono d.V_branch) (fun x hx ↦ hwp x (d.V_branch hx)) d.S d.gap_pos
    (fun x hx ↦ d.inner_gap x (Or.inr hx)) k K' hε

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_PlacedTotalResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology
noncomputable section

theorem PlacedEnvelopeData.seeded_residual_of_seed_support_oai {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {r a : ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} {T : ℝ} (d : PlacedEnvelopeData g r a K T)
    (ha : 0 ≤ a) (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ g seedCoordBranch)
    (hs : ∀ x ∈ seedCoordBranch, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ seedCoordBranch, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiffOn ℝ ∞ w seedCoordBranch)
    (hwp : ∀ x ∈ seedCoordBranch, 0 < w x)
    (hseedSupport : ∀ n, tsupport (realSourceResidual g w (seedEigenvalue n)
      (seedCoordinateField n)) ⊆ K) (k0 K' : ℕ) :
    ∃ b : LocalCompactWaveData g w d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set _root_.OAI.Yau.Jets.Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∀ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let v := gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
            let u := fun x ↦ seedCoordinateField n x+v x
            let R := realSourceResidual g w (seedEigenvalue n)
            ContDiff ℝ ∞ u ∧
            R u = (fun x ↦ R (seedCoordinateField n) x+R v x) ∧
            tsupport (R u) ⊆ Q ∧
            (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k (R u) x = 0) ∧
            (coeff ∈ coefficientEvent (n:ℝ) → ∀ x : _root_.OAI.Yau.Jets.Coord,
              DerivativeBound k0 (R u) x
                (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) := by
  obtain ⟨b,hb,C,hC,Q,hQ,hQΩ,hUQ,hrandom⟩ := d.random_residual ha hg hs hp w hw hwp k0 K'
  have hKU : K ⊆ closure d.U := fun x hx ↦ subset_closure (d.C_U (d.inner_C (Or.inr hx)))
  have hKB : K ⊆ seedCoordBranch := hKU.trans d.closure_U_branch
  have hQB : Q ⊆ seedCoordBranch := hQΩ.trans (subset_closure.trans
    (d.closure_Ω_patch.trans (subset_closure.trans (d.patch_V.trans d.V_branch))))
  have hseed := d.seed_residual ha hK hg hs hp w hw hwp k0 K' (show (0:ℝ)<1 by norm_num)
  refine ⟨b,hb,1+C,by linarith,Q,hQ,hQΩ,hUQ,hKU.trans hUQ,?_⟩
  filter_upwards [hrandom,hseed,b.estimates] with n hn hsn hbn
  obtain ⟨hfin,hn⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff
  let V := fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2
  let v := gaussianWaveField V coeff
  let u := fun x ↦ seedCoordinateField n x+v x
  let R := realSourceResidual g w (seedEigenvalue n)
  have hV (i : SourceGrid d.U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hbn (latticeFrame b.cover subset_closure n i.1,i.2)).1
  have hv : ContDiff ℝ ∞ v := gaussianWaveField_contDiff V coeff hV
  have hsmooth := seedCoordinateField_smooth n
  have hlam : (seedEigenvalue n:ℂ) = (4:ℂ)*(n:ℂ)^2+6*(n:ℂ) := by
    simp [seedEigenvalue]
  have hr := hn coeff
  have hvs : tsupport v ⊆ Q := hr.1
  have he : R u = fun x ↦ R (seedCoordinateField n) x+R v x :=
    realSourceResidual_add_supported seedCoordBranch_open g hg hs hp w hw hwp
      (seedEigenvalue n) _ v hsmooth hv (hvs.trans hQB)
  have hRs : tsupport (R (seedCoordinateField n)) ⊆ Q :=
    (hseedSupport n).trans (hKU.trans (hUQ.trans interior_subset))
  have hRv : tsupport (R v) ⊆ Q := by
    dsimp only [R]
    unfold realSourceResidual
    simpa only [← hlam] using hr.2.1
  have htotal : tsupport (R u) ⊆ Q := by
    apply closure_minimal _ hQ.isClosed
    intro x hx
    by_contra hxQ
    apply hx
    simp only [he]
    rw [image_eq_zero_of_notMem_tsupport (fun hz ↦ hxQ (hRs hz)),
      image_eq_zero_of_notMem_tsupport (fun hz ↦ hxQ (hRv hz)),add_zero]
  change ContDiff ℝ ∞ u ∧ _
  refine ⟨hsmooth.add hv,he,htotal,?_,?_⟩
  · intro x hx k
    exact iteratedFDeriv_zero_off_tsupport htotal hx k
  · intro hc x
    by_cases hx : x ∈ K
    ·
      have hsb : DerivativeBound k0 (R (seedCoordinateField n)) x
          ((n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x)) := by
        dsimp only [R]
        unfold realSourceResidual
        simpa only [one_mul] using hsn x hx
      have hrb : DerivativeBound k0 (R v) x
          (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x)) := by
        dsimp only [R]
        unfold realSourceResidual
        simpa only [← hlam] using (hr.2.2.2 hc).2 x
      have h := realSourceResidual_add_bound seedCoordBranch_open g hg hs hp w hw hwp
        (seedEigenvalue n) _ v hsmooth hv (hvs.trans hQB) (hKB hx) k0 _ _ hsb hrb
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | ring
    · have hz : R (seedCoordinateField n) =ᶠ[𝓝 x] (fun _ ↦ 0) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hseedSupport n h))
      have heq : R u =ᶠ[𝓝 x] R v := by
        filter_upwards [hz] with z hz
        simp only [he,hz,zero_add]
      have hrb : DerivativeBound k0 (R v) x
          (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x)) := by
        dsimp only [R]
        unfold realSourceResidual
        simpa only [← hlam] using (hr.2.2.2 hc).2 x
      intro j hj
      rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
      apply (hrb j hj).trans
      gcongr
      linarith

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.PlacedEnvelopeData.seeded_residual_of_seed_support_oai := @OAI.Yau.Target.PlacedEnvelopeData.seeded_residual_of_seed_support_oai
