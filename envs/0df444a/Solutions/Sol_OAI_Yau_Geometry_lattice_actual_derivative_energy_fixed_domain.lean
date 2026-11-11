-- Prove2me | solution 1 for OAI.Yau.Geometry.lattice_actual_derivative_energy_fixed_domain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:28:01.302283+00:00
-- url     : https://prove2.me/submissions/19126c00-5f50-491e-8c8b-4a2f5ceea5d0

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_lattice_logarithmic_jet_estimates
import Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_lattice_main_coefficient_jets

section
-- module Solutions.OAIQ237_NY.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

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

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

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

theorem smooth_spatial_iteratedFDeriv (f : P → E → F)
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (k : ℕ) :
    ContDiff ℝ ∞ (fun z : P × E ↦ iteratedFDeriv ℝ k (f z.1) z.2) := by
  induction k with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def] using
      (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp hf
  | succ k ih =>
    have h := smooth_spatial_fderiv (fun p x ↦ iteratedFDeriv ℝ k (f p) x) ih
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ E) F).symm.contDiff.comp h

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
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ExponentialWaveBounds
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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FirstJetNonvanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section

lemma covector_norm_le_source (L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) :
    ‖L‖ ≤ 4*sourceEuclideanNorm (fun i ↦ L (Pi.single i 1)) := by
  have hnorm := sourceEuclideanNorm_nonneg (fun i ↦ L (Pi.single i 1))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv : v = ∑ i : Fin 4, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  have he : L v = ∑ i : Fin 4, v i*L (Pi.single i 1) := by
    conv_lhs => rw [hv]
    simp
  have hc (i : Fin 4) : |L (Pi.single i 1)| ≤ sourceEuclideanNorm (fun j ↦ L (Pi.single j 1)) :=
    (norm_le_pi_norm (fun j ↦ L (Pi.single j 1)) i).trans (norm_le_sourceEuclideanNorm _)
  rw [he]
  calc
    _ ≤ ∑ i : Fin 4, |v i| * |L (Pi.single i 1)| := by
      simpa only [norm_mul,Real.norm_eq_abs] using norm_sum_le (Finset.univ : Finset (Fin 4))
        (fun i ↦ v i*L (Pi.single i 1))
    _ ≤ ∑ _ : Fin 4, ‖v‖*sourceEuclideanNorm (fun j ↦ L (Pi.single j 1)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (norm_le_pi_norm v i) (hc i) (abs_nonneg _) (norm_nonneg v)
    _ = _ := by norm_num <;> ring

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

lemma source_covector_le_norm (L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) :
    sourceEuclideanNorm (fun i ↦ L (Pi.single i 1)) ≤ 2*‖L‖ := by
  apply (sourceEuclideanNorm_le _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg L)).mpr
  intro i
  simpa only [Pi.norm_single,norm_one,mul_one] using L.le_opNorm (Pi.single i (1:ℝ))

lemma metric_frequency_annulus (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (μ B : ℝ) (hμ : 0 < μ) (hB : 0 < B) (hg : ‖g‖ ≤ B)
    (hc : ∀ v, μ*‖v‖^2 ≤ g v v) (q : _root_.OAI.Yau.Jets.Coord) (sx sy : ℝ)
    (hx : 0 < sx) (hy : 0 < sy) (hlen : g q q = sy^2)
    (hrlo : sx/2 ≤ sy) (hrhi : sy ≤ 2*sx) :
    Real.sqrt μ/8 ≤ sourceEuclideanNorm (sourceFrequency g q sx) ∧
      sourceEuclideanNorm (sourceFrequency g q sx) ≤ 4*B/Real.sqrt μ := by
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hs2 := Real.sq_sqrt hμ.le
  have hq : ‖q‖ ≤ sy/Real.sqrt μ := by
    apply (le_div_iff₀ hs).mpr
    have hh := hc q
    rw [hlen] at hh
    nlinarith [norm_nonneg q]
  let l := sourceEuclideanNorm (fun i ↦ g q (Pi.single i 1))
  have hl : 0 ≤ l := sourceEuclideanNorm_nonneg _
  have hlo : Real.sqrt μ*sy ≤ 4*l := by
    have he := ((le_abs_self (g q q)).trans ((g q).le_opNorm q)).trans
      (mul_le_mul_of_nonneg_right (covector_norm_le_source (g q)) (norm_nonneg q))
    rw [hlen] at he
    have he' : sy^2 ≤ 4*l*(sy/Real.sqrt μ) := he.trans
      (mul_le_mul_of_nonneg_left hq (by positivity))
    have hh := mul_le_mul_of_nonneg_right he' hs.le
    have hid : (4*l*(sy/Real.sqrt μ))*Real.sqrt μ = 4*l*sy := by field_simp
    rw [hid] at hh
    nlinarith
  have hhi : l ≤ 2*B*(sy/Real.sqrt μ) := by
    apply (source_covector_le_norm (g q)).trans
    have he := (g.le_opNorm q).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg q))
    calc
      _ ≤ 2*(B*‖q‖) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ = 2*B*‖q‖ := by ring
      _ ≤ _ := by gcongr
  have hid : sourceFrequency g q sx = sx⁻¹ • (fun i ↦ g q (Pi.single i 1)) := by
    ext i
    simp only [sourceFrequency,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  rw [hid,sourceEuclideanNorm_smul,abs_of_pos (inv_pos.mpr hx)]
  change Real.sqrt μ/8 ≤ sx⁻¹*l ∧ sx⁻¹*l ≤ 4*B/Real.sqrt μ
  have hmul : sx⁻¹*l = l/sx := by ring
  rw [hmul]
  constructor
  · apply (le_div_iff₀ hx).mpr
    nlinarith
  · apply (div_le_iff₀ hx).mpr
    apply hhi.trans
    calc
      _ ≤ 2*B*((2*sx)/Real.sqrt μ) := by gcongr
      _ = (4*B/Real.sqrt μ)*sx := by ring

theorem compact_metric_frequency_bounds (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    {H : Set _root_.OAI.Yau.Jets.Coord} (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ κ > 0, ∃ K > 0, ∀ y ∈ H, ∀ q : _root_.OAI.Yau.Jets.Coord, ∀ sx sy : ℝ,
      0 < sx → 0 < sy → g y q q = sy^2 → sx/2 ≤ sy → sy ≤ 2*sx →
      κ ≤ sourceEuclideanNorm (sourceFrequency (g y) q sx) ∧
        sourceEuclideanNorm (sourceFrequency (g y) q sx) ≤ K := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  obtain ⟨μ,hμ,B,hB,hb⟩ := uniform_metric_coercivity (fun y : H ↦ g y)
    (continuousOn_iff_continuous_domRestrict.mp hg) (fun y ↦ hp y y.property)
  refine ⟨Real.sqrt μ/8,by positivity,4*B/Real.sqrt μ,by positivity,?_⟩
  intro y hy q sx sy hx hs hlen hlo hhi
  exact metric_frequency_annulus (g y) μ B hμ hB (hb ⟨y,hy⟩).1
    (hb ⟨y,hy⟩).2 q sx sy hx hs hlen hlo hhi

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledCoordinates
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

lemma rescaling_radius_bound {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) :
    0 ≤ (N*s)⁻¹ ∧ (N*s)⁻¹ ≤ 1 ∧ N*(N*s)⁻¹ ≤ 1 := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  refine ⟨by positivity,(inv_le_one₀ (mul_pos hN0 hs0)).mpr
    (one_le_mul_of_one_le_of_one_le hN hs),?_⟩
  have he : N*(N*s)⁻¹ = s⁻¹ := by field_simp
  rw [he]
  exact (inv_le_one₀ hs0).mpr hs

theorem compact_rescaled_envelope_bound (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (R : ℝ) (hR : 0 ≤ R) :
    ∃ L > 0, ∀ (N s : ℝ), 1 ≤ N → 1 ≤ s → ∀ x ∈ Q,
      ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R →
        |N*(S (x+(N*s)⁻¹ • v)-S x)| ≤ L := by
  obtain ⟨B,hB,hBQ⟩ := hQ.isBounded.exists_pos_norm_le
  let P := Metric.closedBall (0:_root_.OAI.Yau.Jets.Coord) (B+R+1)
  have hP : IsCompact P := isCompact_closedBall _ _
  obtain ⟨A,hA,hAP⟩ := (hP.image (hS.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨A*(R+1),by positivity,?_⟩
  intro N s hN hs x hx v hv
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  obtain ⟨hr0,hr1,hNr⟩ := rescaling_radius_bound hN hs
  have hxP : x ∈ P := by
    change dist x 0 ≤ B+R+1
    rw [dist_zero_right]
    linarith [hBQ x hx]
  have hd : ‖(x+(N*s)⁻¹ • v)-x‖ = (N*s)⁻¹*‖v‖ := by
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr0]
  have hzP : x+(N*s)⁻¹ • v ∈ P := by
    change dist (x+(N*s)⁻¹ • v) 0 ≤ B+R+1
    rw [dist_zero_right]
    have ht := norm_le_norm_sub_add (x+(N*s)⁻¹ • v) x
    rw [hd] at ht
    have hb : (N*s)⁻¹*‖v‖ ≤ R :=
      (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)).trans (by simpa using hv)
    linarith [hBQ x hx]
  have h := (convex_closedBall (0:_root_.OAI.Yau.Jets.Coord) (B+R+1)).norm_image_sub_le_of_norm_fderiv_le
    (fun _ _ ↦ (hS.differentiable (by simp)).differentiableAt)
    (fun y hy ↦ hAP _ ⟨y,hy,rfl⟩) hxP hzP
  rw [hd] at h
  change |S (x+(N*s)⁻¹ • v)-S x| ≤ A*((N*s)⁻¹*‖v‖) at h
  rw [abs_mul,abs_of_pos hN0]
  calc
    _ ≤ N*(A*((N*s)⁻¹*‖v‖)) := mul_le_mul_of_nonneg_left h hN0.le
    _ = A*(N*(N*s)⁻¹)*‖v‖ := by ring
    _ ≤ A*1*R := by gcongr
    _ ≤ _ := by nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledSeedBounds
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

lemma rescaledSeedNormalizer_smooth (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (Function.uncurry (rescaledSeedNormalizer S)) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ S) := hS.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact Complex.ofRealCLM.contDiff.comp
    ((contDiff_fst.snd.neg.mul ((hd.comp contDiff_fst.fst).clm_apply contDiff_snd)).exp)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_NormalizedRescaling
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

lemma affine_rescaling_derivative_le (f : _root_.OAI.Yau.Jets.Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (x v : _root_.OAI.Yau.Jets.Coord) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f (x+r • z)) v‖ ≤
      ‖iteratedFDeriv ℝ k f (x+r • v)‖ := by
  let L : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord := r • ContinuousLinearMap.id ℝ _root_.OAI.Yau.Jets.Coord
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖r • z‖ ≤ 1*‖z‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)
  change ‖iteratedFDeriv ℝ k ((fun z ↦ f (x+z)) ∘ L) v‖ ≤ _
  have htrans : ContDiff ℝ ∞ (fun z : _root_.OAI.Yau.Jets.Coord ↦ f (x+z)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [L.iteratedFDeriv_comp_right htrans v
    (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)),iteratedFDeriv_comp_add_left]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏ _ : Fin k, ‖L‖) ≤ 1 := by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg L) hL
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)

lemma normalizedRescaling_square_bound (f : _root_.OAI.Yau.Jets.Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) (N s σ : ℝ)
    (hN : 1 ≤ N) (hs : 1 ≤ s) (hσ : 0 < σ) (x v : _root_.OAI.Yau.Jets.Coord) (d : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ j, j ≤ d → ‖iteratedFDeriv ℝ j (rescaledSeedNormalizer S (x,s⁻¹)) v‖ ≤ A)
    (k : ℕ) (hk : k ≤ d) :
    ‖iteratedFDeriv ℝ k (normalizedRescaling f S N s σ x) v‖^2 ≤
      (2^d*A)^2*(∑ j : Fin (d+1), ‖iteratedFDeriv ℝ j.val f (x+(N*s)⁻¹ • v)‖^2)/σ^2 := by
  let E : ℝ := ∑ j : Fin (d+1), ‖iteratedFDeriv ℝ j.val f (x+(N*s)⁻¹ • v)‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hj (j : ℕ) (hjd : j ≤ d) : ‖iteratedFDeriv ℝ j f (x+(N*s)⁻¹ • v)‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact Finset.single_le_sum (f := fun i : Fin (d+1) ↦
      ‖iteratedFDeriv ℝ i.val f (x+(N*s)⁻¹ • v)‖^2)
      (fun i _ ↦ sq_nonneg _) (Finset.mem_univ (⟨j,by omega⟩ : Fin (d+1)))
  obtain ⟨hr0,hr1,_⟩ := rescaling_radius_bound hN hs
  let amp := rescaledSeedNormalizer S (x,s⁻¹)
  let F : _root_.OAI.Yau.Jets.Coord → ℂ := fun z ↦ f (x+(N*s)⁻¹ • z)
  have hamp : ContDiff ℝ ∞ amp := (rescaledSeedNormalizer_smooth S hS).comp
    (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ F := hf.comp (contDiff_const.add (contDiff_id.const_smul _))
  have hprod := mul_derivative_power_bound hamp hF k v hA (by norm_num : (0:ℝ) ≤ 1)
    (N := 1) (w := 1)
    (fun j hjk ↦ by simpa using ha j (hjk.trans hk))
    (fun j hjk ↦ by simpa only [one_pow,mul_one] using
      (affine_rescaling_derivative_le f hf x v hr0 hr1 j).trans (hj j (hjk.trans hk)))
  simp only [one_pow,mul_one] at hprod
  have hp : (2:ℝ)^k ≤ 2^d := pow_le_pow_right₀ (by norm_num) hk
  have hb : ‖iteratedFDeriv ℝ k (fun z ↦ amp z*F z) v‖ ≤ (2^d*A)*Real.sqrt E :=
    hprod.trans (by gcongr)
  have he : normalizedRescaling f S N s σ x = fun z ↦ (σ⁻¹:ℂ) • (amp z*F z) := by
    funext z
    simp only [normalizedRescaling,smul_eq_mul,amp,F,mul_assoc]
  rw [he,iteratedFDeriv_const_smul_apply' ((hamp.mul hF).of_le (by
    exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,norm_smul,
    norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσ]
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ σ⁻¹*‖iteratedFDeriv ℝ k (fun z ↦ amp z*F z) v‖)
    (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hσ.le)) 2
  refine h.trans_eq ?_
  rw [mul_pow,mul_pow,Real.sq_sqrt hE]
  dsimp [E]
  ring

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_PlaneWaveJets
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

lemma planeWave_smooth (k : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (s : ℝ) : ContDiff ℝ ∞ (planeWave k s) := by
  unfold planeWave
  have hh : ContDiff ℝ ∞ (fun v ↦ ((k v/s:ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (k.contDiff.div_const s)
  exact Complex.contDiff_exp.comp (contDiff_const.mul hh)

lemma planeWave_derivative_bound (k : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {s B : ℝ}
    (hs : 1 ≤ s) (hB : 1 ≤ B) (hk : ‖k‖ ≤ B) (d : ℕ) (v : _root_.OAI.Yau.Jets.Coord) :
    ‖iteratedFDeriv ℝ d (planeWave k s) v‖ ≤ d.factorial*B^d := by
  let L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ := s⁻¹ • (Complex.I • Complex.ofRealCLM.comp k)
  have he : planeWave k s = Complex.exp ∘ L := by
    funext z
    simp [planeWave,L,Complex.real_smul,div_eq_mul_inv,mul_comm,mul_left_comm]
  have hL : ‖L‖ ≤ B := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    intro z
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hi : s⁻¹ ≤ 1 := (inv_le_one₀ hs0).mpr hs
    calc
      ‖L z‖ = s⁻¹*‖k z‖ := by simp [L,abs_of_pos hs0]
      _ ≤ 1*(B*‖z‖) := mul_le_mul hi ((k.le_opNorm z).trans (by gcongr)) (norm_nonneg _) zero_le_one
      _ = _ := by ring
  rw [he]
  have h := norm_iteratedFDeriv_comp_le (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞))
    (L.contDiff (n := ∞)) (n := d) (by exact_mod_cast (show (d:ℕ∞) ≤ ⊤ from le_top)) v
    (C := 1) (D := B)
    (fun j hj ↦ by
      rw [norm_iteratedFDeriv_complex_exp]
      simp [L,Complex.real_smul])
    (fun j hj hjd ↦ by
      by_cases hj1 : j = 1
      · subst j; simpa only [norm_iteratedFDeriv_one,L.fderiv,pow_one] using hL
      · rw [iteratedFDeriv_linear_high L v (by omega),norm_zero]
        positivity)
  simpa only [mul_one] using h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FrequencyDerivativeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma planeWave_divided_frequency (k : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (s : ℝ) :
    planeWave k s = planeWave (s⁻¹ • k) 1 := by
  ext v
  simp [planeWave, div_eq_mul_inv, mul_comm]

lemma planeWave_frequency_derivative_bound (k : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (s : ℝ)
    {B : ℝ} (hB : 1 ≤ B)
    (hk : sourceEuclideanNorm (fun j ↦ k (Pi.single j 1)/s) ≤ B)
    (d : ℕ) (v : _root_.OAI.Yau.Jets.Coord) :
    ‖iteratedFDeriv ℝ d (planeWave k s) v‖ ≤ d.factorial*(4*B)^d := by
  have hnorm : ‖s⁻¹ • k‖ ≤ 4*B := by
    apply (covector_norm_le_source (s⁻¹ • k)).trans
    have he : (fun j ↦ (s⁻¹ • k) (Pi.single j 1)) =
        fun j ↦ k (Pi.single j 1)/s := by
      ext j
      simp [div_eq_mul_inv,mul_comm]
    rw [he]
    linarith
  rw [planeWave_divided_frequency]
  exact planeWave_derivative_bound _ (by norm_num) (by linarith) hnorm d v

lemma weighted_planeWave_derivative_bound (z : ℂ) (k : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (s : ℝ)
    {B : ℝ} (hB : 1 ≤ B)
    (hk : sourceEuclideanNorm (fun j ↦ k (Pi.single j 1)/s) ≤ B)
    (d : ℕ) (v : _root_.OAI.Yau.Jets.Coord) :
    ‖iteratedFDeriv ℝ d (fun u ↦ z*planeWave k s u) v‖ ≤
      ‖z‖*(d.factorial*(4*B)^d) := by
  change ‖iteratedFDeriv ℝ d (z • planeWave k s) v‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply ((planeWave_smooth k s).of_le
    (by exact_mod_cast (show (d:ℕ∞) ≤ ⊤ from le_top))).contDiffAt, norm_smul]
  exact mul_le_mul_of_nonneg_left (planeWave_frequency_derivative_bound k s hB hk d v) (norm_nonneg _)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianTailBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open Filter
open scoped BigOperators Topology
noncomputable section

lemma finite_gaussian_tail {ι : Type*} [Fintype ι] (d f : ι → ℝ)
    {a R B r : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hd : ∀ i, 0 ≤ d i) (hf : ∀ i, f i ≤ R*Real.exp (-2*a*(d i)^2))
    (hs : ∑ i, Real.exp (-a*(d i)^2) ≤ B) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ r < d i), f i ≤
      R*B*Real.exp (-a*r^2) := by
  classical
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i ↦ r < d i),
        (R*Real.exp (-a*r^2))*Real.exp (-a*(d i)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hri := (Finset.mem_filter.mp hi).2.le
      apply (hf i).trans
      simp only [mul_assoc,← Real.exp_add]
      gcongr
      have hh := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hr (hd i)).2 hri) ha
      nlinarith
    _ ≤ ∑ i, (R*Real.exp (-a*r^2))*Real.exp (-a*(d i)^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ by positivity)
    _ = (R*Real.exp (-a*r^2))*∑ i, Real.exp (-a*(d i)^2) := by rw [Finset.mul_sum]
    _ ≤ (R*Real.exp (-a*r^2))*B := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

lemma main_center_scale (N : ℝ) (hN : 0 < N) :
    N*(N^(-5/12:ℝ))^2 = N^(1/6:ℝ) := by
  calc
    _ = N^(1:ℝ)*N^(-5/6:ℝ) := by
      rw [← Real.rpow_mul_natCast hN.le]
      norm_num
    _ = _ := by rw [← Real.rpow_add hN]; norm_num

lemma tendsto_main_center_tail (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ Real.exp (-a*(n:ℝ)^(1/6:ℝ))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n:ℝ)^(1/6:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/6)).comp tendsto_natCast_atTop_atTop
  exact Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos ha)).mpr hpow)

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ShiftedGaussianSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open scoped BigOperators
noncomputable section

lemma summable_integer_exponential {a : ℝ} (ha : 0 < a) :
    Summable (fun z : ℤ ↦ Real.exp (-a * |(z:ℝ)|)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa [mul_comm] using
    (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha))

lemma shifted_square_lower (x : ℝ) (z : ℤ) :
    |((z-⌊x⌋ : ℤ):ℝ)| ≤ (x-(z:ℝ))^2+2 := by
  have h0 := Int.floor_le x
  have h1 := Int.lt_floor_add_one x
  have ht : |((z-⌊x⌋ : ℤ):ℝ)| ≤ |(z:ℝ)-x|+|x-(⌊x⌋:ℝ)| := by
    simpa only [Int.cast_sub,sub_add_sub_cancel] using abs_add_le ((z:ℝ)-x) (x-(⌊x⌋:ℝ))
  rw [abs_of_nonneg (by linarith : 0 ≤ x-(⌊x⌋:ℝ))] at ht
  nlinarith [sq_nonneg (|(z:ℝ)-x|-1),sq_abs ((z:ℝ)-x)]

theorem finite_shifted_gaussian_sum {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ (x : ℝ) (s : Finset ℤ),
      ∑ z ∈ s, Real.exp (-a*(x-(z:ℝ))^2) ≤ C := by
  let f : ℤ → ℝ := fun z ↦ Real.exp (-a*|(z:ℝ)|)
  have hf : Summable f := summable_integer_exponential ha
  have hsum : 0 < ∑' z, f z := (lt_of_lt_of_le (Real.exp_pos _) (hf.le_tsum 0 (fun _ _ ↦ Real.exp_nonneg _)))
  refine ⟨Real.exp (2*a)*(∑' z, f z),mul_pos (Real.exp_pos _) hsum,?_⟩
  intro x s
  calc
    _ ≤ ∑ z ∈ s, Real.exp (2*a)*f (z-⌊x⌋) := by
      apply Finset.sum_le_sum
      intro z _
      dsimp [f]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (shifted_square_lower x z) ha.le
      nlinarith
    _ = Real.exp (2*a)*∑ z ∈ s.image (fun z ↦ z-⌊x⌋), f z := by
      rw [Finset.mul_sum,Finset.sum_image]
      intro u _ v _ huv
      exact sub_left_injective huv
    _ ≤ Real.exp (2*a)*(∑' z, f z) := by
      gcongr
      exact hf.sum_le_tsum _ (fun _ _ ↦ Real.exp_nonneg _)

theorem finite_shifted_gaussian_sum_pi {d : ℕ} {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ (x : Fin d → ℝ) (s : Finset (Fin d → ℤ)),
      ∑ z ∈ s, Real.exp (-a*∑ i, (x i-(z i:ℝ))^2) ≤ C := by
  classical
  obtain ⟨C,hC,hb⟩ := finite_shifted_gaussian_sum ha
  refine ⟨C^d,pow_pos hC d,?_⟩
  intro x s
  let t : Fin d → Finset ℤ := fun i ↦ s.image (fun z ↦ z i)
  have hsub : s ⊆ Fintype.piFinset t := by
    intro z hz
    exact Fintype.mem_piFinset.mpr (fun i ↦ Finset.mem_image.mpr ⟨z,hz,rfl⟩)
  calc
    _ = ∑ z ∈ s, ∏ i, Real.exp (-a*(x i-(z i:ℝ))^2) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum,Real.exp_sum]
    _ ≤ ∑ z ∈ Fintype.piFinset t, ∏ i, Real.exp (-a*(x i-(z i:ℝ))^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ = ∏ i, ∑ z ∈ t i, Real.exp (-a*(x i-(z:ℝ))^2) :=
      (Finset.prod_univ_sum t (fun i z ↦ Real.exp (-a*(x i-(z:ℝ))^2))).symm
    _ ≤ ∏ _i : Fin d, C := by
      apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
      intro i _
      exact hb (x i) (t i)
    _ = C^d := by simp

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ScaledLatticeGaussianSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability
noncomputable section

lemma scaled_lattice_squared_distance {n : ℕ} (hn : 0 < n) (x : _root_.OAI.Yau.Jets.Coord)
    (z : Fin 4 → ℤ) :
    (n:ℝ)*(sourceEuclideanNorm (x-scaledLatticePoint n z))^2 =
      ∑ i, (Real.sqrt n*x i-(z i:ℝ))^2 := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ n by positivity)
  rw [sourceEuclideanNorm,Real.sq_sqrt (by positivity),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (n:ℝ)*(x i-(n:ℝ)^(-1/2:ℝ)*(z i:ℝ))^2 = _
  rw [lattice_scale_eq_inv_sqrt]
  field_simp
  nlinarith [hs2]

theorem source_lattice_gaussian_sum {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ (U : Set _root_.OAI.Yau.Jets.Coord) (n : ℕ), 0 < n → ∀ [Fintype (SourceGrid U n)],
      ∀ x : _root_.OAI.Yau.Jets.Coord, ∑ z : SourceGrid U n,
        Real.exp (-a*(n:ℝ)*(sourceEuclideanNorm (x-scaledLatticePoint n z))^2) ≤ C := by
  classical
  obtain ⟨C,hC,hb⟩ := finite_shifted_gaussian_sum_pi (d := 4) ha
  refine ⟨C,hC,?_⟩
  intro U n hn hfin x
  let s : Finset (Fin 4 → ℤ) := Finset.univ.image (fun z : SourceGrid U n ↦ z.val)
  have h := hb (fun i ↦ Real.sqrt n*x i) s
  rw [Finset.sum_image (by intro u _ v _ huv; exact Subtype.ext huv)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [mul_assoc,scaled_lattice_squared_distance hn]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeVarianceUpper
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

lemma latticeVariance_nonneg (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)] (x : _root_.OAI.Yau.Jets.Coord) :
    0 ≤ a.latticeVariance hUD n x := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma latticeSigma_sq (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)] (x : _root_.OAI.Yau.Jets.Coord) :
    (a.latticeSigma hUD n x)^2 = a.latticeVariance hUD n x :=
  Real.sq_sqrt (a.latticeVariance_nonneg hUD n x)

theorem lattice_derivative_square_sum_bound (hUD : U ⊆ D) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x : _root_.OAI.Yau.Jets.Coord,
      ∀ k : Fin (k0+1),
      ∑ i : SourceGrid U n × Fin 3,
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x) := by
  obtain ⟨B,hB,hgauss⟩ := source_lattice_gaussian_sum (show 0 < 2*a.beams.c by have := a.beams.c_pos; positivity)
  refine ⟨3*a.beams.Cw^2*B,by have := a.beams.Cw_pos; positivity,?_⟩
  filter_upwards [a.estimates,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro hfin x k
  let R := a.beams.Cw^2*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)
  have hR : 0 ≤ R := by dsimp [R] <;> positivity
  have hb (i : SourceGrid U n × Fin 3) :
      ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        R*Real.exp (-(2*a.beams.c)*(n:ℝ)*(sourceEuclideanNorm (x-scaledLatticePoint n i.1))^2) := by
    have h := ((hn (latticeFrame a.cover hUD n i.1,i.2)).2.2.2.2 x).1 k
    simp only [latticeFrame_center] at h
    change ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖ ≤ _ at h
    have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
    refine hh.trans_eq ?_
    dsimp [R]
    rw [mul_pow,mul_pow,← Real.exp_nat_mul,← pow_mul]
    simp only [mul_assoc,← Real.exp_add]
    congr 2 <;> ring_nf
  calc
    _ ≤ ∑ i : SourceGrid U n × Fin 3, R*Real.exp (-(2*a.beams.c)*(n:ℝ)*
        (sourceEuclideanNorm (x-scaledLatticePoint n i.1))^2) := Finset.sum_le_sum (fun i _ ↦ hb i)
    _ = 3*R*∑ z : SourceGrid U n, Real.exp (-(2*a.beams.c)*(n:ℝ)*
        (sourceEuclideanNorm (x-scaledLatticePoint n z))^2) := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [← Finset.mul_sum,← Finset.mul_sum,mul_assoc]
      dsimp [R]
      ring
    _ ≤ 3*R*B := mul_le_mul_of_nonneg_left (hgauss U n hnpos x) (by positivity)
    _ = _ := by dsimp [R] <;> ring

theorem lattice_variance_upper_bound (hUD : U ⊆ D) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x : _root_.OAI.Yau.Jets.Coord,
      a.latticeVariance hUD n x ≤ C*Real.exp (2*(n:ℝ)*S x) := by
  obtain ⟨C,hC,hb⟩ := a.lattice_derivative_square_sum_bound hUD
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with n hn
  intro hfin x
  calc
    a.latticeVariance hUD n x =
        ∑ i : SourceGrid U n × Fin 3,
          ‖iteratedFDeriv ℝ 0 (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z : ℝ ↦ z^2)
        (norm_iteratedFDeriv_zero (𝕜 := ℝ)
          (f := latticeWave a.cover a.beams hUD n i.1 i.2) (x := x)).symm
    _ ≤ _ := by simpa only [Fin.val_zero,mul_zero,pow_zero,mul_one] using! hn x 0

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeDerivativeTail
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
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_derivative_tail_bound (hUD : U ⊆ D) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x : _root_.OAI.Yau.Jets.Coord,
      ∀ k : Fin (k0+1), ∀ r : ℝ, 0 ≤ r →
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          r < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)*Real.exp (-a.beams.c*(n:ℝ)*r^2) := by
  classical
  obtain ⟨B,hB,hgauss⟩ := source_lattice_gaussian_sum a.beams.c_pos
  refine ⟨3*a.beams.Cw^2*B,by have := a.beams.Cw_pos; positivity,?_⟩
  filter_upwards [a.estimates,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro hfin x k r hr
  let d : SourceGrid U n × Fin 3 → ℝ := fun i ↦ sourceEuclideanNorm (x-scaledLatticePoint n i.1)
  let R := a.beams.Cw^2*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)
  have hb (i : SourceGrid U n × Fin 3) :
      ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        R*Real.exp (-2*(a.beams.c*(n:ℝ))*(d i)^2) := by
    have h := ((hn (latticeFrame a.cover hUD n i.1,i.2)).2.2.2.2 x).1 k
    simp only [latticeFrame_center] at h
    change ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖ ≤ _ at h
    refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq ?_
    dsimp [R,d]
    rw [mul_pow,mul_pow,← Real.exp_nat_mul,← pow_mul]
    simp only [mul_assoc,← Real.exp_add]
    congr 2 <;> ring_nf
  have hg : ∑ i : SourceGrid U n × Fin 3, Real.exp (-(a.beams.c*(n:ℝ))*(d i)^2) ≤ 3*B := by
    dsimp [d]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [← Finset.mul_sum]
    norm_num only [Nat.cast_ofNat]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [neg_mul] using hgauss U n hnpos x
  have hh := finite_gaussian_tail d
    (fun i ↦ ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2)
    (by have := a.beams.c_pos; positivity : 0 ≤ a.beams.c*(n:ℝ))
    (by dsimp [R]; positivity : 0 ≤ R) hr (fun i ↦ sourceEuclideanNorm_nonneg _) hb hg
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [R]
  simp only [neg_mul]
  ring

theorem lattice_nonmain_derivative_bound (hUD : U ⊆ D) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x : _root_.OAI.Yau.Jets.Coord,
      ∀ k : Fin (k0+1),
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2 ≤
        C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := a.lattice_derivative_tail_bound hUD
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro hfin x k
  have h := hn x k ((n:ℝ)^(-5/12:ℝ)) (by positivity)
  rwa [mul_assoc (-a.beams.c),main_center_scale _ (by exact_mod_cast hnpos)] at h

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeVarianceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_variance_lower_bound (hUD : U ⊆ D) (hU : IsOpen U)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x ∈ Q,
      c*Real.exp (2*(n:ℝ)*S x) ≤ a.latticeVariance hUD n x := by
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,c,hc,C,hC,hb⟩ :=
    a.lattice_logarithmic_jet_estimates hUD 2 (by norm_num)
  obtain ⟨r,hr,hinner⟩ := compact_inner_ball hQ hU hQU
  refine ⟨c^2,pow_pos hc 2,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℕ),
    eventually_nat_frequency (half_scale_eventually 2 1 r hr)] with n hn hnpos hsmall
  intro hfin x hx
  have hd := (norm_le_sourceEuclideanNorm _).trans (rounded_lattice_distance hnpos x)
  have hmem : scaledLatticePoint n (roundedLatticeIndex n x) ∈ U :=
    hinner x hx (by simpa only [mem_closedBall,dist_eq_norm] using hd.trans hsmall.2.1)
  let z : SourceGrid U n := ⟨roundedLatticeIndex n x,hmem⟩
  have hd' : ‖x-scaledLatticePoint n z‖ ≤ 2*(n:ℝ)^(-1/2:ℝ) := by
    rw [norm_sub_rev]; exact hd
  have hl := (hn z 0 x hd').2.2.2.2.1
  have hle : c*Real.exp ((n:ℝ)*S x) ≤ ‖latticeWave a.cover a.beams hUD n z 0 x‖ := by
    have hh := mul_le_mul_of_nonneg_right hl.1 (Real.exp_nonneg ((n:ℝ)*S x))
    simpa only [mul_assoc,← Real.exp_add,neg_mul,neg_add_cancel,Real.exp_zero,mul_one] using hh
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ c*Real.exp ((n:ℝ)*S x)) hle 2
  have he : (c*Real.exp ((n:ℝ)*S x))^2 = c^2*Real.exp (2*(n:ℝ)*S x) := by
    rw [mul_pow,← Real.exp_nat_mul]
    congr 2
    ring
  rw [he] at hs
  apply hs.trans
  unfold latticeVariance
  exact Finset.single_le_sum (fun i _ ↦ sq_nonneg ‖latticeWave a.cover a.beams hUD n i.1 i.2 x‖)
    (Finset.mem_univ (z,(0:Fin 3)))

theorem lattice_sigma_comparison (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ x ∈ Q, c*Real.exp ((n:ℝ)*S x) ≤ a.latticeSigma hUD n x ∧
        a.latticeSigma hUD n x ≤ C*Real.exp ((n:ℝ)*S x) := by
  obtain ⟨c,hc,hlo⟩ := a.lattice_variance_lower_bound hUD hU hQ hQU
  obtain ⟨C,hC,hup⟩ := a.lattice_variance_upper_bound hUD
  refine ⟨Real.sqrt c,Real.sqrt_pos.mpr hc,Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  filter_upwards [hlo,hup,eventually_gt_atTop (0:ℕ)] with n hl hu hn
  have := finite_source_grid hUb hn
  let hfin := Fintype.ofFinite (SourceGrid U n)
  refine ⟨hfin,?_⟩
  intro x hx
  have hl' := hl x hx
  have hu' := hu x
  have hs := a.latticeSigma_sq hUD n x
  have hnon : 0 ≤ a.latticeSigma hUD n x := Real.sqrt_nonneg _
  have he : (Real.exp ((n:ℝ)*S x))^2 = Real.exp (2*(n:ℝ)*S x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hc2 := Real.sq_sqrt hc.le
  have hC2 := Real.sq_sqrt hC.le
  constructor
  · apply (sq_le_sq₀ (by positivity) hnon).mp
    rw [mul_pow,hc2,he,hs]
    exact hl'
  · apply (sq_le_sq₀ hnon (by positivity)).mp
    rw [mul_pow,hC2,he,hs]
    exact hu'

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeNormalizedWeights
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
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma latticeAlpha_sum_sq (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x : _root_.OAI.Yau.Jets.Coord) (s : Finset (SourceGrid U n × Fin 3)) :
    ∑ i ∈ s, ‖a.latticeAlpha hUD n x i‖^2 =
      (∑ i ∈ s, ‖latticeWave a.cover a.beams hUD n i.1 i.2 x‖^2) / a.latticeVariance hUD n x := by
  simp only [latticeAlpha,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ a.latticeSigma hUD n x from Real.sqrt_nonneg _),
    div_pow,a.latticeSigma_sq,Finset.sum_div]

lemma latticeAlpha_total (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x : _root_.OAI.Yau.Jets.Coord) (hv : 0 < a.latticeVariance hUD n x) :
    ∑ i, ‖a.latticeAlpha hUD n x i‖^2 = 1 := by
  rw [a.latticeAlpha_sum_sq]
  exact div_self hv.ne'

theorem latticeAlpha_nonmain_bound (hUD : U ⊆ D) (hU : IsOpen U)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)], ∀ x ∈ Q,
      0 < a.latticeVariance hUD n x ∧
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖a.latticeAlpha hUD n x i‖^2 ≤ C*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)) := by
  classical
  obtain ⟨c,hc,hlo⟩ := a.lattice_variance_lower_bound hUD hU hQ hQU
  obtain ⟨C,hC,htail⟩ := a.lattice_nonmain_derivative_bound hUD
  refine ⟨C/c,div_pos hC hc,?_⟩
  filter_upwards [hlo,htail] with n hl ht
  intro hfin x hx
  have hv : 0 < a.latticeVariance hUD n x :=
    lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hl x hx)
  refine ⟨hv,?_⟩
  rw [a.latticeAlpha_sum_sq]
  apply (div_le_iff₀ hv).mpr
  have h := ht x (0 : Fin (k0+1))
  simp only [Fin.val_zero,mul_zero,pow_zero,mul_one] at h
  change (∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
      (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
    ‖iteratedFDeriv ℝ 0 (latticeWave a.cover a.beams hUD n i.1 i.2) x‖^2) ≤ _ at h
  simp only [norm_iteratedFDeriv_zero] at h
  refine h.trans ?_
  have hh := mul_le_mul_of_nonneg_left (hl x hx)
    (by positivity : 0 ≤ (C/c)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)))
  calc
    _ = ((C/c)*Real.exp (-a.beams.c*(n:ℝ)^(1/6:ℝ)))*(c*Real.exp (2*(n:ℝ)*S x)) := by field_simp
    _ ≤ _ := hh

theorem latticeAlpha_main_mass (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, (∑ i, ‖a.latticeAlpha hUD n x i‖^2 = 1) ∧
        1-ε ≤ ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)),
          ‖a.latticeAlpha hUD n x i‖^2 := by
  classical
  obtain ⟨C,hC,hb⟩ := a.latticeAlpha_nonmain_bound hUD hU hQ hQU
  have hlim := (tendsto_main_center_tail a.beams.c a.beams.c_pos).const_mul C
  simp only [mul_zero] at hlim
  filter_upwards [hb,hlim.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)] with n hn hsmall hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  refine ⟨hfin,?_⟩
  intro x hx
  obtain ⟨hv,ht⟩ := hn x hx
  have hall := a.latticeAlpha_total hUD n x hv
  refine ⟨hall,?_⟩
  have he := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (SourceGrid U n × Fin 3)))
    (fun i ↦ sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ))
    (fun i ↦ ‖a.latticeAlpha hUD n x i‖^2)
  simp only [not_le,hall] at he
  linarith

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledDerivativeMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma normalizedRescaling_smooth (f : _root_.OAI.Yau.Jets.Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (N s sigma : ℝ) (x : _root_.OAI.Yau.Jets.Coord) :
    ContDiff ℝ ∞ (normalizedRescaling f S N s sigma x) := by
  have hn : ContDiff ℝ ∞ (rescaledSeedNormalizer S (x,s⁻¹)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_const.mul (fderiv ℝ S x).contDiff).exp)
  exact (contDiff_const.mul hn).mul
    (hf.comp (contDiff_const.add (contDiff_id.const_smul _)))

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

lemma shifted_center_distance {x y z : _root_.OAI.Yau.Jets.Coord} {r : ℝ}
    (hfar : r < sourceEuclideanNorm (x-y)) (hshift : ‖z-x‖ ≤ r/4) :
    r/4 < sourceEuclideanNorm (z-y) := by
  have ht : ‖x-y‖ ≤ ‖z-x‖+‖z-y‖ := by
    calc
      _ = ‖(x-z)+(z-y)‖ := by congr 1; abel
      _ ≤ ‖x-z‖+‖z-y‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev x z]
  have he := sourceEuclideanNorm_le (x-y)
  have hn := norm_le_sourceEuclideanNorm (z-y)
  linarith

lemma main_radius_times_frequency {N : ℝ} (hN : 0 < N) :
    N*N^(-5/12:ℝ) = N^(7/12:ℝ) := by
  calc
    _ = N^(1:ℝ)*N^(-5/12:ℝ) := by rw [Real.rpow_one]
    _ = N^((1:ℝ)+(-5/12)) := (Real.rpow_add hN _ _).symm
    _ = _ := by norm_num

theorem eventually_shifted_center_distance (R : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : ℝ), 1 ≤ s → ∀ (x y v : _root_.OAI.Yau.Jets.Coord), ‖v‖ ≤ R →
      (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-y) →
      (n:ℝ)^(-5/12:ℝ)/4 < sourceEuclideanNorm (x+((n:ℝ)*s)⁻¹ • v-y) := by
  have ht : Tendsto (fun n : ℕ ↦ (n:ℝ)^(7/12:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 7/12)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (4*R)),eventually_gt_atTop (0:ℕ)]
    with n hn hnpos
  intro s hs x y v hv hfar
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hd := rescaling_displacement_bound (x := x) hn1 hs hv
  rw [← main_radius_times_frequency hn0] at hn
  apply shifted_center_distance hfar
  nlinarith

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

lemma compact_main_scale_comparison (s : _root_.OAI.Yau.Jets.Coord → ℝ) {H : Set _root_.OAI.Yau.Jets.Coord} (hH : IsCompact H)
    (hs : ContinuousOn s H) (hlo : ∀ x ∈ H, 2 ≤ s x) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ H, ∀ y ∈ H,
      sourceEuclideanNorm (x-y) ≤ (n:ℝ)^(-5/12:ℝ) →
      s x/2 ≤ s y ∧ s y ≤ 2*s x := by
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp
    (hH.uniformContinuousOn_of_continuous hs) 1 (by norm_num)
  have ht : Tendsto (fun n : ℕ ↦ (n:ℝ)^(-5/12:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/12)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn
  intro x hx y hy hnear
  have hh := hd x hx y hy (by
    rw [dist_eq_norm]
    exact ((norm_le_sourceEuclideanNorm _).trans hnear).trans_lt hn)
  rw [Real.dist_eq] at hh
  have h := abs_lt.mp hh
  have hx2 := hlo x hx
  constructor <;> linarith

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

include a in
lemma source_main_scale_comparison {H : Set _root_.OAI.Yau.Jets.Coord} (hH : IsCompact H) (hHD : H ⊆ D) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ H, ∀ y ∈ H,
      sourceEuclideanNorm (x-y) ≤ (n:ℝ)^(-5/12:ℝ) →
      sourceSignScale g S x/2 ≤ sourceSignScale g S y ∧
        sourceSignScale g S y ≤ 2*sourceSignScale g S x :=
  compact_main_scale_comparison _ hH (a.source_sign_scale_continuousOn hHD)
    (fun x hx ↦ a.source_sign_scale_lower x (hHD hx))

lemma original_direction_length (t : a.cover.Parameter) (j : Fin 3) :
    g (coverSourceCenter a.cover t) (a.cover.triple.q t j) (a.cover.triple.q t j) =
      (sourceSignScale g S (coverSourceCenter a.cover t))^2 := by
  have he := a.cover.triple.length t j
  have hp := a.positive_G (coverSourceCenter a.cover t) _ (a.nonzero_gradient _ (a.cover.center t).property)
  change 0 < a.G (coverSourceCenter a.cover t)
    (metricGradient a.G a.A (coverSourceCenter a.cover t))
    (metricGradient a.G a.A (coverSourceCenter a.cover t)) at hp
  change a.G (coverSourceCenter a.cover t) (a.cover.triple.q t j) (a.cover.triple.q t j) =
    a.G (coverSourceCenter a.cover t) (metricGradient a.G a.A (coverSourceCenter a.cover t))
      (metricGradient a.G a.A (coverSourceCenter a.cover t))+4 at he
  have hh : (sourceSignScale a.G a.A (coverSourceCenter a.cover t))^2 =
      a.G (coverSourceCenter a.cover t) (metricGradient a.G a.A (coverSourceCenter a.cover t))
        (metricGradient a.G a.A (coverSourceCenter a.cover t))+4 :=
    Real.sq_sqrt (by linarith)
  rw [← hh,a.source_sign_scale_eq (coverSourceCenter a.cover t)
      (a.centers_E (a.cover.center t).property),
    (a.center_identifications t).1] at he
  exact he

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FixedDomainLatticeFrequencyAnnulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_main_frequency_annulus_fixed_domain
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ κ > 0, ∃ B > 0, ∀ (w S : _root_.OAI.Yau.Jets.Coord → ℝ) (D U : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
      U ⊆ H → ∀ᶠ n : ℕ in atTop, ∀ x ∈ D, ∀ i : SourceGrid U n × Fin 3,
      sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      κ ≤ sourceEuclideanNorm (sourceFrequency (g (scaledLatticePoint n i.1))
        (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2) (sourceSignScale g S x)) ∧
      sourceEuclideanNorm (sourceFrequency (g (scaledLatticePoint n i.1))
        (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2) (sourceSignScale g S x)) ≤ B := by
  obtain ⟨κ,hκ,B,hB,hmetric⟩ := compact_metric_frequency_bounds g hH hg hp
  refine ⟨κ,hκ,B,hB,?_⟩
  intro w S D U m J K k0 a hD hDH hUD hUH
  filter_upwards [a.source_main_scale_comparison hD Subset.rfl] with n hn
  intro x hx i hi
  have hy : scaledLatticePoint n i.1 ∈ D := hUD i.1.property
  have hr := hn x hx _ hy hi
  have hx0 : 0 < sourceSignScale g S x := by linarith [a.source_sign_scale_lower x hx]
  have hy0 : 0 < sourceSignScale g S (scaledLatticePoint n i.1) := by
    linarith [a.source_sign_scale_lower _ (hUD i.1.property)]
  apply hmetric _ (hDH hy) _ _ _ hx0 hy0 _ hr.1 hr.2
  simpa only [latticeFrame_center] using a.original_direction_length (latticeFrame a.cover hUD n i.1) i.2

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticePlaneWaveJets
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

theorem lattice_main_jet_approximation (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (R : ℝ) (hR : 0 ≤ R) (d0 : ℕ) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R → ∀ k, k ≤ d0 →
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
        sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)),
        ‖iteratedFDeriv ℝ k (fun z ↦ normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2) S n s
          (a.latticeSigma hUD n x) x z - a.latticeAlpha hUD n x i *
          planeWave (g (scaledLatticePoint n i.1) (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)) s z) v‖^2 ≤ e := by
  classical
  filter_upwards [a.lattice_main_coefficient_jets hUD R hR d0 (Real.sqrt e) (Real.sqrt_pos.mpr he),
    a.latticeAlpha_main_mass hUD hU hUb hQ hQU 1 zero_lt_one] with n hn hmass
  obtain ⟨hfin,hmass⟩ := hmass
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv k hk
  let I := Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
    sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ))
  have hsum : ∑ i ∈ I, ‖a.latticeAlpha hUD n x i‖^2 ≤ 1 := by
    rw [← (hmass x hx).1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)
  calc
    _ ≤ ∑ i ∈ I, e*‖a.latticeAlpha hUD n x i‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hb := hn x (hUD (hQU hx)) s hs (a.latticeSigma hUD n x) v hv i (Finset.mem_filter.mp hi).2 k hk
      have hh := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rw [mul_pow,Real.sq_sqrt he.le] at hh
      exact hh
    _ = e*(∑ i ∈ I, ‖a.latticeAlpha hUD n x i‖^2) := by rw [Finset.mul_sum]
    _ ≤ e := by nlinarith

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeNonmainDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open Filter
open scoped Topology

lemma tendsto_polynomial_main_center_tail (k : ℕ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ (n:ℝ)^k*Real.exp (-a*(n:ℝ)^(1/6:ℝ))) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n:ℝ)^(1/6:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/6)).comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (6*(k:ℝ)) a ha).comp hpow
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [Function.comp_def]
  rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ n)]
  rw [show (1/6:ℝ)*(6*(k:ℝ)) = (k:ℝ) by ring,Real.rpow_natCast]

end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ShiftedLatticeTail
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
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_shifted_nonmain_bound (hUD : U ⊆ D) (hS : ContDiff ℝ ∞ S)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∀ [Fintype (SourceGrid U n)],
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R → ∀ k : Fin (k0+1),
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2)
          (x+((n:ℝ)*s)⁻¹ • v)‖^2 ≤
        C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)*
          Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ)) := by
  classical
  obtain ⟨B,hB,htail⟩ := a.lattice_derivative_tail_bound hUD
  obtain ⟨L,hL,hshift⟩ := compact_rescaled_envelope_bound S hS hQ R hR
  refine ⟨B*Real.exp (2*L),by positivity,?_⟩
  filter_upwards [htail,eventually_shifted_center_distance R,eventually_gt_atTop (0:ℕ)]
    with n hn hdist hnpos
  intro hfin x hx s hs v hv k
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  let z := x+((n:ℝ)*s)⁻¹ • v
  let r : ℝ := (n:ℝ)^(-5/12:ℝ)
  have hsub : Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
      r < sourceEuclideanNorm (x-scaledLatticePoint n i.1)) ⊆
      Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
      r/4 < sourceEuclideanNorm (z-scaledLatticePoint n i.1)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdist s hs x _ v hv (Finset.mem_filter.mp hi).2⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ ↦
    sq_nonneg ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2) z‖)
  have he : -a.beams.c*(n:ℝ)*(r/4)^2 = -(a.beams.c/16)*(n:ℝ)^(1/6:ℝ) := by
    calc
      _ = -(a.beams.c/16)*((n:ℝ)*r^2) := by ring
      _ = _ := by rw [main_center_scale _ hn0]
  have hb := hn z k (r/4) (by dsimp [r] <;> positivity)
  rw [he] at hb
  have hexp : Real.exp (2*(n:ℝ)*S z) ≤ Real.exp (2*(n:ℝ)*S x)*Real.exp (2*L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := (le_abs_self _).trans (hshift n s hn1 hs x hx v hv)
    dsimp [z]
    nlinarith
  apply (hsum.trans hb).trans
  calc
    _ ≤ B*(n:ℝ)^(2*k.val)*(Real.exp (2*(n:ℝ)*S x)*Real.exp (2*L))*
        Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ)) := by gcongr
    _ = _ := by ring

theorem lattice_shifted_nonmain_negligible (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R → ∀ k : Fin (k0+1),
      (∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val (latticeWave a.cover a.beams hUD n i.1 i.2)
          (x+((n:ℝ)*s)⁻¹ • v)‖^2) / (a.latticeSigma hUD n x)^2 ≤ ε := by
  classical
  obtain ⟨c,hc,hlo⟩ := a.lattice_variance_lower_bound hUD hU hQ hQU
  obtain ⟨C,hC,htail⟩ := a.lattice_shifted_nonmain_bound hUD hS hQ R hR
  have hlim := (tendsto_polynomial_main_center_tail (2*k0) (a.beams.c/16)
    (by have := a.beams.c_pos; positivity)).const_mul (C/c)
  simp only [mul_zero] at hlim
  filter_upwards [hlo,htail,hlim.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)]
    with n hl ht hsmall hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv k
  have hv0 : 0 < a.latticeVariance hUD n x :=
    lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hl x hx)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hp : (n:ℝ)^(2*k.val) ≤ (n:ℝ)^(2*k0) :=
    pow_le_pow_right₀ hn1 (by have := k.isLt; omega)
  rw [a.latticeSigma_sq]
  apply le_trans _ hsmall.le
  apply (div_le_iff₀ hv0).mpr
  have hh := mul_le_mul_of_nonneg_left (hl x hx)
    (by positivity : 0 ≤ (C/c)*((n:ℝ)^(2*k0)*Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ))))
  calc
    _ ≤ C*(n:ℝ)^(2*k.val)*Real.exp (2*(n:ℝ)*S x)*
        Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ)) := ht x hx s hs v hv k
    _ ≤ C*(n:ℝ)^(2*k0)*Real.exp (2*(n:ℝ)*S x)*
        Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ)) := by gcongr
    _ = ((C/c)*((n:ℝ)^(2*k0)*Real.exp (-(a.beams.c/16)*(n:ℝ)^(1/6:ℝ))))*
        (c*Real.exp (2*(n:ℝ)*S x)) := by field_simp
    _ ≤ _ := hh

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_RescaledLatticeTail
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

theorem rescaled_lattice_nonmain_negligible (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R → ∀ k : Fin (k0+1),
      ∑ i ∈ Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
          (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1)),
        ‖iteratedFDeriv ℝ k.val
          (normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2)
            S n s (a.latticeSigma hUD n x) x) v‖^2 ≤ ε := by
  classical
  obtain ⟨A,hA,hamp⟩ := compact_smooth_derivative_bound (rescaledSeedNormalizer S) k0
    (fun j _ ↦ (smooth_spatial_iteratedFDeriv _ (rescaledSeedNormalizer_smooth S hS) j).continuous)
    (Q ×ˢ Icc (0:ℝ) 1) (hQ.prod isCompact_Icc) R
  let C : ℝ := (2^k0*A)^2
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hkpos : (0:ℝ) < k0+1 := by positivity
  obtain ⟨c,hc,B,hB,hsigma⟩ := a.lattice_sigma_comparison hUD hU hUb hQ hQU
  have htail := a.lattice_shifted_nonmain_negligible hUD hU hUb hQ hQU hS R hR
    (ε/(C*((k0:ℝ)+1))) (by positivity)
  filter_upwards [htail,hsigma,a.estimates,eventually_gt_atTop (0:ℕ)]
    with n hn hσ hest hnpos
  obtain ⟨hfin,ht⟩ := hn
  obtain ⟨hfin',hσ⟩ := hσ
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv k
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hσ0 : 0 < a.latticeSigma hUD n x :=
    lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hσ x hx).1
  have ha := hamp (x,s⁻¹) ⟨hx,by positivity,(inv_le_one₀ hs0).mpr hs⟩ v hv
  let F := Finset.univ.filter (fun i : SourceGrid U n × Fin 3 ↦
    (n:ℝ)^(-5/12:ℝ) < sourceEuclideanNorm (x-scaledLatticePoint n i.1))
  have hb (i : SourceGrid U n × Fin 3) := normalizedRescaling_square_bound
    (latticeWave a.cover a.beams hUD n i.1 i.2)
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
    S hS n s _ hn1 hs hσ0 x v k0 A hA.le ha k.val (by omega)
  apply (Finset.sum_le_sum (fun i (_ : i ∈ F) ↦ hb i)).trans
  calc
    _ = C*∑ j : Fin (k0+1), ((∑ i ∈ F,
        ‖iteratedFDeriv ℝ j.val (latticeWave a.cover a.beams hUD n i.1 i.2)
          (x+((n:ℝ)*s)⁻¹ • v)‖^2)/(a.latticeSigma hUD n x)^2) := by
      dsimp only [C]
      simp only [Finset.mul_sum,Finset.sum_div,mul_div_assoc]
      rw [Finset.sum_comm]
    _ ≤ C*∑ _j : Fin (k0+1), ε/(C*((k0:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ ↦ ht x hx s hs v hv j)) hC.le
    _ = ε := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      field_simp

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeFullPlaneWaveApprox
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

theorem lattice_full_jet_approximation (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (R : ℝ) (hR : 0 ≤ R) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R → ∀ k : Fin (k0+1),
      ∑ i : SourceGrid U n × Fin 3,
        ‖iteratedFDeriv ℝ k.val (fun z ↦
          normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2) S n s
            (a.latticeSigma hUD n x) x z - a.latticePlaneWaveCoefficient hUD n x s i z) v‖^2 ≤ e := by
  classical
  filter_upwards [a.lattice_main_jet_approximation hUD hU hUb hQ hQU R hR k0 (e/2) (by positivity),
    a.rescaled_lattice_nonmain_negligible hUD hU hUb hQ hQU hS R hR (e/2) (by positivity)]
    with n hmain htail
  obtain ⟨hfin,hm⟩ := hmain
  obtain ⟨hfin',ht⟩ := htail
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv k
  let P := fun i : SourceGrid U n × Fin 3 ↦
    sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ)
  let err := fun i : SourceGrid U n × Fin 3 ↦
    ‖iteratedFDeriv ℝ k.val (fun z ↦
      normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2) S n s
        (a.latticeSigma hUD n x) x z-a.latticePlaneWaveCoefficient hUD n x s i z) v‖^2
  have hm' : ∑ i ∈ Finset.univ.filter P, err i ≤ e/2 := by
    have hh := hm x hx s hs v hv k.val (by omega)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i hi
    have hp := (Finset.mem_filter.mp hi).2
    dsimp only [P] at hp
    simp only [err,latticePlaneWaveCoefficient,ite_eq_left hp]
  have ht' : ∑ i ∈ Finset.univ.filter (fun i ↦ ¬P i), err i ≤ e/2 := by
    have hh := ht x hx s hs v hv k
    convert hh using 1
    · apply Finset.sum_congr
      · ext i; simp only [P,Finset.mem_filter,not_le]
      · intro i hi
        have hp := (Finset.mem_filter.mp hi).2
        simp only [err,latticePlaneWaveCoefficient,ite_eq_right (not_le.mpr hp),sub_zero]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ) P err
  change ∑ i, err i ≤ e
  linarith

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticePlaneWaveEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
namespace LocalCompactWaveData
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma latticePlaneWaveCoefficient_smooth (hUD : U ⊆ D) (n : ℕ)
    [Fintype (SourceGrid U n)] (x : _root_.OAI.Yau.Jets.Coord) (s : ℝ) (i : SourceGrid U n × Fin 3) :
    ContDiff ℝ ∞ (a.latticePlaneWaveCoefficient hUD n x s i) := by
  classical
  unfold latticePlaneWaveCoefficient
  split_ifs
  · exact contDiff_const.mul (planeWave_smooth _ _)
  · exact contDiff_const

lemma latticePlaneWaveCoefficient_energy (hUD : U ⊆ D) (n : ℕ)
    [Fintype (SourceGrid U n)] (x : _root_.OAI.Yau.Jets.Coord) (s : ℝ) {B : ℝ} (hB : 1 ≤ B)
    (hm : ∑ i : SourceGrid U n × Fin 3, ‖a.latticeAlpha hUD n x i‖^2 ≤ 1)
    (hb : ∀ i : SourceGrid U n × Fin 3,
      sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      sourceEuclideanNorm (sourceFrequency (g (scaledLatticePoint n i.1))
        (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2) s) ≤ B)
    (k : ℕ) (v : _root_.OAI.Yau.Jets.Coord) :
    ∑ i : SourceGrid U n × Fin 3,
      ‖iteratedFDeriv ℝ k (a.latticePlaneWaveCoefficient hUD n x s i) v‖^2 ≤
        (k.factorial*(4*B)^k)^2 := by
  classical
  have hbound (i : SourceGrid U n × Fin 3) :
      ‖iteratedFDeriv ℝ k (a.latticePlaneWaveCoefficient hUD n x s i) v‖ ≤
        ‖a.latticeAlpha hUD n x i‖*(k.factorial*(4*B)^k) := by
    unfold latticePlaneWaveCoefficient
    split_ifs with hi
    · exact weighted_planeWave_derivative_bound _ _ s hB (hb i hi) k v
    · simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      positivity
  calc
    _ ≤ ∑ i : SourceGrid U n × Fin 3,
        (‖a.latticeAlpha hUD n x i‖*(k.factorial*(4*B)^k))^2 :=
      Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hbound i) 2)
    _ = (∑ i : SourceGrid U n × Fin 3, ‖a.latticeAlpha hUD n x i‖^2)*
        (k.factorial*(4*B)^k)^2 := by simp only [mul_pow,Finset.sum_mul]
    _ ≤ _ := by nlinarith [sq_nonneg ((k.factorial:ℝ)*(4*B)^k)]
end LocalCompactWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FixedDomainLatticePlaneWaveEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_planeWave_derivative_energy_fixed_domain
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) (d : ℕ) :
    ∃ C > 0, ∀ (w S : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0), IsCompact D → D ⊆ H → ∀ (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∀ v : _root_.OAI.Yau.Jets.Coord, ∀ k : ℕ, k ≤ d →
        ∑ i : SourceGrid U n × Fin 3,
          ‖iteratedFDeriv ℝ k
            (a.latticePlaneWaveCoefficient hUD n x (sourceSignScale g S x) i) v‖^2 ≤ C := by
  obtain ⟨κ,hκ,B,hB,hann⟩ := lattice_main_frequency_annulus_fixed_domain g hH hg hp
  let B' := max 1 B
  let C := ((d.factorial:ℝ)*(4*B')^d)^2
  have hB' : 1 ≤ B' := le_max_left _ _
  have h4 : 1 ≤ 4*B' := by linarith
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  intro w S D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
  filter_upwards [hann w S D U m J K k0 a hD hDH hUD hUH,
    a.latticeAlpha_main_mass hUD hU hUb hQ hQU (1/2) (by norm_num)] with n hn hm
  obtain ⟨hfin,hm⟩ := hm
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v k hk
  apply (a.latticePlaneWaveCoefficient_energy hUD n x _ hB' (by rw [(hm x hx).1])
    (fun i hi ↦ ((hn x (hUD (hQU hx)) i hi).2).trans (le_max_right _ _)) k v).trans
  have hf : (k.factorial:ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hk
  have hpow := pow_le_pow_right₀ h4 hk
  dsimp [C]
  gcongr

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeActualDerivativeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma norm_square_le_two_sub_add {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a‖^2 ≤ 2*‖a-b‖^2+2*‖b‖^2 := by
  have h := norm_add_le (a-b) b
  rw [sub_add_cancel] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg a) h 2
  nlinarith [sq_nonneg (‖a-b‖-‖b‖)]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FixedDomainLatticeActualDerivativeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_actual_derivative_energy_fixed_domain_oai
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) (d : ℕ) :
    ∃ C > 0, ∀ (w S : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0), IsCompact D → D ⊆ H → ∀ (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ContDiff ℝ ∞ S → d ≤ k0 →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ 2 → ∀ k : ℕ, k ≤ d →
        ∑ i : SourceGrid U n × Fin 3,
          ‖iteratedFDeriv ℝ k (normalizedRescaling
            (latticeWave a.cover a.beams hUD n i.1 i.2) S n (sourceSignScale g S x)
            (a.latticeSigma hUD n x) x) v‖^2 ≤ C := by
  obtain ⟨C,hC,hplane⟩ := lattice_planeWave_derivative_energy_fixed_domain g hH hg hp d
  refine ⟨2+2*C,by positivity,?_⟩
  intro w S D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hd
  filter_upwards [hplane w S D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU,
    a.lattice_full_jet_approximation hUD hU hUb hQ hQU hS 2 (by norm_num) 1 (by norm_num),
    a.estimates] with n hW he hest
  obtain ⟨hfin,hW⟩ := hW
  obtain ⟨hfin',he⟩ := he
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v hv k hk
  let W := a.latticePlaneWaveCoefficient hUD n x (sourceSignScale g S x)
  let A := fun i : SourceGrid U n × Fin 3 ↦ normalizedRescaling
    (latticeWave a.cover a.beams hUD n i.1 i.2) S n (sourceSignScale g S x)
    (a.latticeSigma hUD n x) x
  have hAs (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (A i) :=
    normalizedRescaling_smooth _ (hest (latticeFrame a.cover hUD n i.1,i.2)).1 _ _ _ _ _
  have hWs (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (W i) :=
    a.latticePlaneWaveCoefficient_smooth _ _ _ _ _
  have hk' : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  have hid (i : SourceGrid U n × Fin 3) :
      iteratedFDeriv ℝ k (fun z ↦ A i z-W i z) v =
        iteratedFDeriv ℝ k (A i) v-iteratedFDeriv ℝ k (W i) v := by
    change iteratedFDeriv ℝ k (A i-W i) v = _
    exact iteratedFDeriv_sub_apply ((hAs i).of_le hk').contDiffAt ((hWs i).of_le hk').contDiffAt
  have herr := he x hx _ (show 1 ≤ sourceSignScale g S x by
    linarith [a.source_sign_scale_lower x (hUD (hQU hx))]) v hv (⟨k,by omega⟩ : Fin (k0+1))
  change (∑ i, ‖iteratedFDeriv ℝ k (fun z ↦ A i z-W i z) v‖^2) ≤ 1 at herr
  simp_rw [hid] at herr
  have hw := hW x hx v k hk
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (SourceGrid U n × Fin 3))) ↦
    norm_square_le_two_sub_add (iteratedFDeriv ℝ k (A i) v) (iteratedFDeriv ℝ k (W i) v))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hb
  change (∑ i, ‖iteratedFDeriv ℝ k (A i) v‖^2) ≤ _
  change (∑ i, ‖iteratedFDeriv ℝ k (W i) v‖^2) ≤ C at hw
  linarith

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.lattice_actual_derivative_energy_fixed_domain_oai := @OAI.Yau.Geometry.lattice_actual_derivative_energy_fixed_domain_oai
