-- Prove2me | solution 1 for OAI.Yau.Geometry.lattice_physical_sign_subballs_fixed_domain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:28:41.750791+00:00
-- url     : https://prove2.me/submissions/390ba2b5-6444-44db-9a2b-84f257d1e73a

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
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
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_lattice_logarithmic_jet_estimates
import Theorems.Thm_OAI_Yau_Geometry_lattice_actual_derivative_energy_fixed_domain
import Theorems.Thm_OAI_Yau_Geometry_lattice_sign_margin_probability_fixed_domain

section
-- module Solutions.OAIQ237_NY.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

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
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianWaveJet
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

lemma oscillatorySeed_contDiff (S T : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (hT : ContDiff ℝ ∞ T) (N : ℝ) : ContDiff ℝ ∞ (oscillatorySeed S T N) :=
  ((contDiff_const.mul hS).exp).mul ((contDiff_const.mul hT).cos)

end
end Yau.Jets

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

lemma sourceEuclideanBall_compact (R : ℝ) : IsCompact {x : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm x ≤ R} := by
  have he : {x : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm x ≤ R} =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)) '' closedBall 0 R := by
    ext x
    simp only [mem_ofPred_eq,mem_image,mem_closedBall,dist_zero_right]
    constructor
    · intro hx
      exact ⟨WithLp.toLp 2 x,by rwa [← sourceEuclideanNorm_eq_norm],rfl⟩
    · rintro ⟨y,hy,rfl⟩
      rw [sourceEuclideanNorm_eq_norm]
      change ‖(WithLp.toLp 2 y.ofLp : EuclideanSpace ℝ (Fin 4))‖ ≤ R
      simpa only [WithLp.toLp_ofLp] using hy
  rw [he]
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).image
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).continuous

lemma sourceEuclideanBall_convex (R : ℝ) : Convex ℝ {x : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm x ≤ R} := by
  intro x hx y hy a b ha hb hab
  change sourceEuclideanNorm (a • x+b • y) ≤ R
  apply (sourceEuclideanNorm_add_le _ _).trans
  rw [sourceEuclideanNorm_smul,sourceEuclideanNorm_smul,abs_of_nonneg ha,abs_of_nonneg hb]
  calc
    _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [← add_mul,hab,one_mul]

lemma source_sign_subballs_inside {tau r : ℝ} (ht : 0 ≤ tau) (_hr : 0 ≤ r)
    (htr : tau+r ≤ 1) (j : Fin 4) :
    (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ r → sourceEuclideanNorm v ≤ 1) ∧
    (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
      sourceEuclideanNorm v ≤ 1) := by
  constructor
  · intro v hv
    linarith
  · intro v hv
    have hh := sourceEuclideanNorm_add_le (v-tau • Pi.single j 1) (tau • Pi.single j 1)
    rw [sub_add_cancel,sourceEuclideanNorm_single,abs_of_nonneg ht] at hh
    linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AnchoredIntervalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section

lemma enorm_le_anchor_lintegral {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖f t‖ₑ ≤ ‖f 0‖ₑ + ∫⁻ u in Icc (-1 : ℝ) 1, ‖deriv f u‖ₑ := by
  have hd : ‖f t - f 0‖ₑ ≤ ∫⁻ u in Icc (-1 : ℝ) 1, ‖deriv f u‖ₑ := by
    by_cases h : 0 ≤ t
    · exact (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn h).trans
        (lintegral_mono_set (Icc_subset_Icc (by norm_num) ht.2))
    · have h' := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn (le_of_not_ge h)
      rw [enorm_sub_rev] at h'
      exact h'.trans (lintegral_mono_set (Icc_subset_Icc ht.1 (by norm_num)))
  calc
    ‖f t‖ₑ = ‖f 0 + (f t-f 0)‖ₑ := by congr 1; ring
    _ ≤ ‖f 0‖ₑ + ‖f t-f 0‖ₑ := enorm_add_le _ _
    _ ≤ _ := add_le_add_right hd _

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AnchoredCubeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open MeasureTheory Set Function
open scoped ENNReal ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma inUnitCube_update {x : ι → ℝ} (hx : InUnitCube x)
    (i : ι) {t : ℝ} (ht : |t| ≤ 1) : InUnitCube (update x i t) := by
  intro j
  by_cases h : j = i
  · subst j; simpa using ht
  · simpa [update_of_ne h] using hx j

lemma enorm_le_cubeControl (f : List ι → (ι → ℝ) → ℝ)
    (hs : ∀ ds, ContDiff ℝ 1 (f ds))
    (hd : ∀ ds i x, fderiv ℝ (f ds) x (Pi.single i 1) = f (i::ds) x)
    (is ds : List ι) (x : ι → ℝ) (hx : InUnitCube x) :
    ‖f ds x‖ₑ ≤ cubeControl f is ds x := by
  induction is generalizing ds x with
  | nil => exact le_rfl
  | cons i is ih =>
    have hder (t : ℝ) : deriv (fun t ↦ f ds (update x i t)) t =
        f (i::ds) (update x i t) := by
      change deriv (f ds ∘ update x i) t = _
      rw [((hs ds).differentiable one_ne_zero (update x i t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_update x i t) |>.deriv]
      exact hd ds i _
    have hh := enorm_le_anchor_lintegral ((hs ds).comp (contDiff_update 1 x i))
      (abs_le.mp (hx i))
    change ‖f ds (update x i (x i))‖ₑ ≤ ‖f ds (update x i 0)‖ₑ +
      ∫⁻ t in Icc (-1:ℝ) 1, ‖deriv (fun t ↦ f ds (update x i t)) t‖ₑ at hh
    rw [update_eq_self] at hh
    simp_rw [hder] at hh
    apply hh.trans
    exact add_le_add (ih ds _ (inUnitCube_update hx i (by norm_num)))
      (lintegral_mono_ae (by
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
        exact ih (i::ds) _ (inUnitCube_update hx i (abs_le.mpr ht))))

omit [Fintype ι] in
lemma cubeControl_congr_base (f : List ι → (ι → ℝ) → ℝ)
    (is ds : List ι) (x y : ι → ℝ) (h : ∀ j, j ∉ is → x j = y j) :
    cubeControl f is ds x = cubeControl f is ds y := by
  induction is generalizing ds x y with
  | nil =>
    have he : x = y := funext (fun j ↦ h j (by simp))
    rw [he]
  | cons i is ih =>
    have he (t : ℝ) (j : ι) (hj : j ∉ is) : update x i t j = update y i t j := by
      by_cases hi : j = i
      · subst j; simp
      · simp only [update_of_ne hi]
        exact h j (by simp [hi,hj])
    simp only [cubeControl]
    rw [ih ds _ _ (he 0)]
    congr 1
    apply lintegral_congr
    intro t
    exact ih (i::ds) _ _ (he t)

lemma enorm_le_cubeControl_zero (f : List ι → (ι → ℝ) → ℝ)
    (hs : ∀ ds, ContDiff ℝ 1 (f ds))
    (hd : ∀ ds i x, fderiv ℝ (f ds) x (Pi.single i 1) = f (i::ds) x)
    (is ds : List ι) (hall : ∀ i, i ∈ is) (x : ι → ℝ) (hx : InUnitCube x) :
    ‖f ds x‖ₑ ≤ cubeControl f is ds 0 := by
  rw [← cubeControl_congr_base f is ds x 0 (fun j hj ↦ (hj (hall j)).elim)]
  exact enorm_le_cubeControl f hs hd is ds x hx

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinatePartialJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma partialJet_smooth (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List ι) : ContDiff ℝ ∞ (partialJet f ds) := by
  induction ds with
  | nil => exact hf
  | cons i ds ih =>
    exact (ih.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

lemma partialJet_eq_iterated (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List ι) (x : ι → ℝ) :
    partialJet f ds x = iteratedFDeriv ℝ ds.length f x (partialDirs ds) := by
  induction ds generalizing x with
  | nil => simp [partialJet,partialDirs,iteratedFDeriv_zero_apply]
  | cons i ds ih =>
    have hh : partialJet f ds = fun x ↦ iteratedFDeriv ℝ ds.length f x (partialDirs ds) :=
      funext ih
    change fderiv ℝ (partialJet f ds) x (Pi.single i 1) = _
    rw [hh]
    symm
    have hdiff := hf.differentiable_iteratedFDeriv (m := ds.length)
      (by exact_mod_cast (show (ds.length:ℕ∞) < ⊤ from WithTop.coe_lt_top _))
    simpa only [List.length_cons,partialDirs,Fin.cons_zero,Fin.tail_cons] using
      (hdiff x).iteratedFDeriv_succ_apply_left' (m := Fin.cons (Pi.single i 1) (partialDirs ds))

lemma partialDirs_norm_le_one (ds : List ι) : ‖partialDirs ds‖ ≤ 1 := by
  induction ds with
  | nil => exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun j ↦ Fin.elim0 j)
  | cons i ds ih =>
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)] at ih ⊢
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · change ‖(Pi.single i (1:ℝ) : ι → ℝ)‖ ≤ 1
      apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
      intro k
      by_cases h : k = i <;> simp [h]
    · simpa [partialDirs] using ih k

end
end Yau.Analysis

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

lemma rescaledSeedPhase_smooth (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0) :
    ContDiff ℝ ∞ (Function.uncurry (rescaledSeedPhase S0 T0)) := by
  have ha : ContDiff ℝ ∞ (fun z : (_root_.OAI.Yau.Jets.Coord × ℝ) × _root_.OAI.Yau.Jets.Coord ↦ z.1.1+z.1.2 • z.2) :=
    contDiff_fst.fst.add (contDiff_fst.snd.smul contDiff_snd)
  exact (Complex.ofRealCLM.contDiff.comp (hS0.comp ha)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hT0.comp ha)))

lemma rescaledSeedNormalizer_smooth (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (Function.uncurry (rescaledSeedNormalizer S)) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ S) := hS.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact Complex.ofRealCLM.contDiff.comp
    ((contDiff_fst.snd.neg.mul ((hd.comp contDiff_fst.fst).clm_apply contDiff_snd)).exp)

lemma rescaledSeed_representation (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ) (N s σ : ℝ) (x : _root_.OAI.Yau.Jets.Coord) :
    rescaledSeed S0 T0 S N s σ x = fun v ↦ σ⁻¹ *
      (rescaledSeedNormalizer S (x,s⁻¹) v *
        waveExp (rescaledSeedPhase S0 T0 (x,(N*s)⁻¹)) N v).re := by
  funext v
  change oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v) /
    (σ*Real.exp (fderiv ℝ S x v / s)) = σ⁻¹ *
      ((Real.exp (-s⁻¹ * fderiv ℝ S x v):ℂ) *
        waveExp (rescaledSeedPhase S0 T0 (x,(N*s)⁻¹)) N v).re
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hw : (waveExp (rescaledSeedPhase S0 T0 (x,(N*s)⁻¹)) N v).re =
      oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v) := by
    simp [waveExp,rescaledSeedPhase,oscillatorySeed,Complex.exp_re]
  rw [hw,neg_mul,Real.exp_neg]
  simp [div_eq_mul_inv,mul_comm,mul_left_comm]

theorem rescaledSeed_derivative_bound (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0) (hS : ContDiff ℝ ∞ S)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ (N s σ : ℝ), 1 ≤ N → 1 ≤ s → 0 < σ →
      ∀ x ∈ Q, ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R →
        ‖iteratedFDeriv ℝ k (rescaledSeed S0 T0 S N s σ x) v‖ ≤
          C*N^k*Real.exp (N*S0 (x+(N*s)⁻¹ • v))/σ := by
  have hp := rescaledSeedPhase_smooth S0 T0 hS0 hT0
  have ha := rescaledSeedNormalizer_smooth S hS
  obtain ⟨D,hD,hd⟩ := compact_smooth_derivative_bound (rescaledSeedPhase S0 T0) k
    (fun j _ ↦ (smooth_spatial_iteratedFDeriv _ hp j).continuous)
    (Q ×ˢ Icc (0:ℝ) 1) (hQ.prod isCompact_Icc) R
  obtain ⟨A,hA,ha'⟩ := compact_smooth_derivative_bound (rescaledSeedNormalizer S) k
    (fun j _ ↦ (smooth_spatial_iteratedFDeriv _ ha j).continuous)
    (Q ×ˢ Icc (0:ℝ) 1) (hQ.prod isCompact_Icc) R
  let B : ℝ := (k.factorial:ℝ)*(D+1)^k
  have hB : 0 < B := by dsimp [B] <;> positivity
  refine ⟨2^k*A*B,by positivity,?_⟩
  intro N s σ hN hs hσ x hx v hv
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hr : (N*s)⁻¹ ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity,(inv_le_one₀ (mul_pos hN0 hs0)).mpr (one_le_mul_of_one_le_of_one_le hN hs)⟩
  have ht : s⁻¹ ∈ Icc (0:ℝ) 1 := ⟨by positivity,(inv_le_one₀ hs0).mpr hs⟩
  let phi := rescaledSeedPhase S0 T0 (x,(N*s)⁻¹)
  let amp := rescaledSeedNormalizer S (x,s⁻¹)
  have hphi : ContDiff ℝ ∞ phi := hp.comp (contDiff_const.prodMk contDiff_id)
  have hamp : ContDiff ℝ ∞ amp := ha.comp (contDiff_const.prodMk contDiff_id)
  have he (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (waveExp phi N) v‖ ≤ B*N^j*Real.exp (N*(phi v).re) := by
    apply (waveExp_derivative_bound hphi j v (by linarith : 1 ≤ D+1) hN
      (fun i _ hi ↦ (hd _ ⟨hx,hr⟩ v hv i (hi.trans hj)).trans (by linarith))).trans
    have hf : (j.factorial:ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hj
    have hpw : (D+1)^j ≤ (D+1)^k := pow_le_pow_right₀ (by linarith) hj
    dsimp [B]
    gcongr
  have hm := mul_derivative_power_bound hamp (waveExp_contDiff hphi N) k v hA.le hN0.le
    (fun j hj ↦ (ha' _ ⟨hx,ht⟩ v hv j hj).trans
      (le_mul_of_one_le_right hA.le (one_le_pow₀ hN))) he
  have hre : ContDiff ℝ ∞ (fun z ↦ (amp z*waveExp phi N z).re) :=
    Complex.reCLM.contDiff.comp (hamp.mul (waveExp_contDiff hphi N))
  rw [rescaledSeed_representation]
  change ‖iteratedFDeriv ℝ k (fun z ↦ σ⁻¹ • (amp z*waveExp phi N z).re) v‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hre.of_le (by
    exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,norm_smul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hσ)]
  have hreal := realPart_iterated_norm_le (fun z ↦ amp z*waveExp phi N z) v
    (hamp.mul (waveExp_contDiff hphi N)).contDiffAt k
  have hh := mul_le_mul_of_nonneg_left (hreal.trans hm) (inv_nonneg.mpr hσ.le)
  simpa [phi,rescaledSeedPhase,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh

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

lemma normalizedRescaling_eq_div (f : _root_.OAI.Yau.Jets.Coord → ℂ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N s σ : ℝ) (x v : _root_.OAI.Yau.Jets.Coord) :
    normalizedRescaling f S N s σ x v =
      f (x+(N*s)⁻¹ • v) / (σ*Real.exp (fderiv ℝ S x v/s):ℝ) := by
  simp only [normalizedRescaling,rescaledSeedNormalizer,neg_mul,Real.exp_neg,
    Complex.ofReal_mul,Complex.ofReal_inv,div_eq_mul_inv,mul_inv_rev]
  rw [show fderiv ℝ S x v * s⁻¹ = s⁻¹ * fderiv ℝ S x v by ring]
  ring

end
end Yau.Geometry

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
-- module Solutions.OAIQ237_NY.NodalSets_Waves_RescaledGaussianField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma rescaledGaussianField_decomposition (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N s σ : ℝ) (x : _root_.OAI.Yau.Jets.Coord) (coeff : ι × Fin 2 → ℝ) (v : _root_.OAI.Yau.Jets.Coord) :
    rescaledGaussianField V S0 T0 S N s σ x coeff v = rescaledSeed S0 T0 S N s σ x v +
      gaussianWaveField (fun i ↦ normalizedRescaling (V i) S N s σ x) coeff v := by
  classical
  simp only [rescaledGaussianField,rescaledSeed,add_div,gaussianWaveField,
    normalizedRescaling_eq_div,← mul_div_assoc,Complex.re_sum,Complex.div_ofReal_re,
    Finset.sum_div]

lemma pairLinearSum_integrable (z : ι → ℂ) : Integrable (pairLinearSum z) gaussianPairs := by
  classical
  unfold pairLinearSum gaussianPairs
  apply integrable_finsetSum
  intro p _
  exact (integrable_eval (μ := fun _ : ι × Fin 2 ↦ gaussianReal 0 1)
    (i := p) IsGaussian.integrable_id).const_mul _

lemma pairLinearSum_mean (z : ι → ℂ) : ∫ coeff, pairLinearSum z coeff ∂gaussianPairs = 0 := by
  classical
  unfold pairLinearSum gaussianPairs
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro p _
    rw [integral_const_mul,integral_eval]
    simp
  · intro p _
    exact (integrable_eval (μ := fun _ : ι × Fin 2 ↦ gaussianReal 0 1)
      (i := p) IsGaussian.integrable_id).const_mul _

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianPairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma pairLinearSum_memLp_two (z : ι → ℂ) : MemLp (pairLinearSum z) 2 gaussianPairs := by
  classical
  unfold pairLinearSum gaussianPairs
  apply memLp_finsetSum
  intro p _
  have hh : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := IsGaussian.memLp_two_id
  exact (hh.comp_measurePreserving (measurePreserving_eval (μ := fun _ : ι × Fin 2 ↦ gaussianReal 0 1) p)).const_mul _

lemma pairLinearSum_mean_square (z : ι → ℂ) (m : ℝ) :
    ∫ coeff, (m+pairLinearSum z coeff)^2 ∂gaussianPairs = m^2+∑ i, ‖z i‖^2 := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have hp := pairLinearSum_memLp_two z
  have hh := variance_eq_sub ((memLp_const m).add hp)
  have hm : ∫ coeff, m+pairLinearSum z coeff ∂gaussianPairs = m := by
    rw [integral_add (integrable_const _) (pairLinearSum_integrable z),pairLinearSum_mean,integral_const]
    simp
  change Var[fun coeff ↦ m+pairLinearSum z coeff;gaussianPairs] =
    (∫ coeff, (m+pairLinearSum z coeff)^2 ∂gaussianPairs) -
      (∫ coeff, m+pairLinearSum z coeff ∂gaussianPairs)^2 at hh
  rw [hm,variance_const_add hp.aestronglyMeasurable,variance_pairLinearSum] at hh
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianDerivativeMoments
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

lemma gaussianWaveField_iterated_apply (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (a : ι × Fin 2 → ℝ)
    (k : ℕ) (x : _root_.OAI.Yau.Jets.Coord) (v : Fin k → _root_.OAI.Yau.Jets.Coord) :
    iteratedFDeriv ℝ k (gaussianWaveField V a) x v =
      pairLinearSum (fun i ↦ iteratedFDeriv ℝ k (V i) x v) a := by
  classical
  let W : _root_.OAI.Yau.Jets.Coord → ℂ := fun z ↦ ∑ i, gaussianCoefficient a i*V i z
  have hW : ContDiff ℝ ∞ W := ContDiff.sum (fun i _ ↦ contDiff_const.mul (hV i))
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  change iteratedFDeriv ℝ k (Complex.reCLM ∘ W) x v = _
  rw [Complex.reCLM.iteratedFDeriv_comp_left hW.contDiffAt hk]
  change (iteratedFDeriv ℝ k W x v).re = _
  dsimp only [W]
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
    ((contDiff_const.mul (hV i)).of_le hk).contDiffAt)]
  simp only [sum_apply,Complex.re_sum,pairLinearSum_eq_complex]
  apply Finset.sum_congr rfl
  intro i _
  change (iteratedFDeriv ℝ k (gaussianCoefficient a i • V i) x v).re = _
  rw [iteratedFDeriv_const_smul_apply ((hV i).of_le hk).contDiffAt]
  rfl

lemma seeded_gaussian_iterated_apply (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (a : ι × Fin 2 → ℝ) (k : ℕ) (x : _root_.OAI.Yau.Jets.Coord) (v : Fin k → _root_.OAI.Yau.Jets.Coord) :
    iteratedFDeriv ℝ k (fun z ↦ seed z+gaussianWaveField V a z) x v =
      iteratedFDeriv ℝ k seed x v +
        pairLinearSum (fun i ↦ iteratedFDeriv ℝ k (V i) x v) a := by
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top)
  change iteratedFDeriv ℝ k (seed + gaussianWaveField V a) x v = _
  rw [iteratedFDeriv_add_apply (hs.of_le hk).contDiffAt
    ((gaussianWaveField_contDiff V a hV).of_le hk).contDiffAt]
  simp only [add_apply,gaussianWaveField_iterated_apply V hV]

lemma seeded_gaussian_derivative_memLp (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (k : ℕ) (x : _root_.OAI.Yau.Jets.Coord) (v : Fin k → _root_.OAI.Yau.Jets.Coord) :
    MemLp (fun a ↦ iteratedFDeriv ℝ k
      (fun z ↦ seed z+gaussianWaveField V a z) x v) 2 gaussianPairs := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  simp_rw [seeded_gaussian_iterated_apply V seed hV hs]
  exact (memLp_const (μ := gaussianPairs (ι := ι)) (p := 2)
    (iteratedFDeriv ℝ k seed x v)).add (pairLinearSum_memLp_two _)

lemma seeded_gaussian_derivative_moment (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (k : ℕ) (x : _root_.OAI.Yau.Jets.Coord) (v : Fin k → _root_.OAI.Yau.Jets.Coord) :
    ∫ a, (iteratedFDeriv ℝ k (fun z ↦ seed z+gaussianWaveField V a z) x v)^2
      ∂gaussianPairs = (iteratedFDeriv ℝ k seed x v)^2 +
        ∑ i, ‖iteratedFDeriv ℝ k (V i) x v‖^2 := by
  simp_rw [seeded_gaussian_iterated_apply V seed hV hs]
  exact pairLinearSum_mean_square _ _

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianPartialMeasurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Yau.Probability MeasureTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma seeded_partial_joint_continuous (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (ds : List (Fin 4)) :
    Continuous (fun z : (ι × Fin 2 → ℝ) × _root_.OAI.Yau.Jets.Coord ↦
      partialJet (fun x ↦ seed x+gaussianWaveField V z.1 x) ds z.2) := by
  have hF (a : ι × Fin 2 → ℝ) := hs.add (gaussianWaveField_contDiff V a hV)
  simp_rw [partialJet_eq_iterated _ (hF _),seeded_gaussian_iterated_apply V seed hV hs]
  have horder : (ds.length : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (show (ds.length:ℕ∞) ≤ ⊤ from le_top)
  have hc {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : _root_.OAI.Yau.Jets.Coord → F) (hf : ContDiff ℝ ∞ f) :
      Continuous (fun z : (ι × Fin 2 → ℝ) × _root_.OAI.Yau.Jets.Coord ↦
        iteratedFDeriv ℝ ds.length f z.2 (partialDirs ds)) :=
    ((hf.continuous_iteratedFDeriv horder).comp continuous_snd).eval continuous_const
  apply (hc seed hs).add
  unfold pairLinearSum
  apply continuous_finsetSum
  intro p _
  apply Continuous.mul
  · split_ifs
    · exact Complex.continuous_re.comp (hc (V p.1) (hV p.1))
    · exact (Complex.continuous_im.comp (hc (V p.1) (hV p.1))).neg
  · exact (continuous_apply p).comp continuous_fst

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSignEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Yau.Probability MeasureTheory Set
open scoped ContDiff
noncomputable section
variable {Ω X : Type*} [TopologicalSpace Ω] [TopologicalSpace X]

lemma isOpen_compact_positive_event (F : Ω → X → ℝ) (K : Set X)
    (hK : IsCompact K) (hF : Continuous (fun z : Ω × X ↦ F z.1 z.2)) :
    IsOpen {a | ∀ x ∈ K, 0 < F a x} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : IsClosed {z : Ω × K | F z.1 z.2 ≤ 0} :=
    isClosed_le (hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      continuous_const
  have hh := isClosedMap_fst_of_compactSpace _ hc
  have he : (Prod.fst '' {z : Ω × K | F z.1 z.2 ≤ 0})ᶜ = {a | ∀ x ∈ K, 0 < F a x} := by
    ext a
    constructor
    · intro ha x hx
      by_contra hn
      exact ha ⟨(a,⟨x,hx⟩),le_of_not_gt hn,rfl⟩
    · intro ha hmem
      obtain ⟨⟨b,x⟩,hh,heq⟩ := hmem
      change b = a at heq
      subst b
      exact (not_le_of_gt (ha x x.property)) hh
  rw [← he]
  exact hh.isOpen_compl

lemma measurable_compact_opposite_signs [MeasurableSpace Ω] [BorelSpace Ω]
    (F : Ω → X → ℝ) (Kpos Kneg : Set X) (hp : IsCompact Kpos) (hn : IsCompact Kneg)
    (hF : Continuous (fun z : Ω × X ↦ F z.1 z.2)) :
    MeasurableSet {a | (∀ x ∈ Kpos, 0 < F a x) ∧ (∀ x ∈ Kneg, F a x < 0)} := by
  have h1 := isOpen_compact_positive_event F Kpos hp hF
  have h2 := isOpen_compact_positive_event (fun a x ↦ -F a x) Kneg hn hF.neg
  simpa only [neg_pos,Set.inter_def,Set.mem_ofPred_eq] using (h1.inter h2).measurableSet

lemma seeded_gaussian_joint_continuous {ι : Type*} [Fintype ι]
    (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) :
    Continuous (fun z : (ι × Fin 2 → ℝ) × _root_.OAI.Yau.Jets.Coord ↦ seed z.2+gaussianWaveField V z.1 z.2) :=
  seeded_partial_joint_continuous V seed hV hs []

lemma source_closed_ball_compact (x : _root_.OAI.Yau.Jets.Coord) (r : ℝ) :
    IsCompact {y : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm (y-x) ≤ r} := by
  have he : {y : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm (y-x) ≤ r} =
      (fun v : _root_.OAI.Yau.Jets.Coord ↦ x+v) '' {v : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm v ≤ r} := by
    ext y
    constructor
    · intro hy
      exact ⟨y-x,hy,add_sub_cancel _ _⟩
    · rintro ⟨v,hv,rfl⟩
      simpa only [add_sub_cancel_left,mem_ofPred_eq] using hv
  rw [he]
  exact (sourceEuclideanBall_compact r).image (continuous_const.add continuous_id)

lemma seeded_gaussian_sign_balls_measurable {ι : Type*} [Fintype ι]
    (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (x y : _root_.OAI.Yau.Jets.Coord) (rpos rneg : ℝ) :
    MeasurableSet {a : ι × Fin 2 → ℝ |
      (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (v-x) ≤ rpos → 0 < seed v+gaussianWaveField V a v) ∧
      (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (v-y) ≤ rneg → seed v+gaussianWaveField V a v < 0)} :=
  measurable_compact_opposite_signs _ _ _ (source_closed_ball_compact x rpos)
    (source_closed_ball_compact y rneg) (seeded_gaussian_joint_continuous V seed hV hs)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CubeControlExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open MeasureTheory Set Function
open scoped ENNReal
noncomputable section
variable {ι Ω : Type*} [DecidableEq ι] [MeasurableSpace Ω]

lemma measurable_coordinate_update {f : Ω → (ι → ℝ)} {g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (i : ι) :
    Measurable (fun a ↦ update (f a) i (g a)) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j = i
  · subst j; simpa only [update_self] using hg
  · simpa only [update_of_ne h, Function.comp_def] using (measurable_pi_apply j).comp hf

lemma cubeControl_measurable (f : Ω → List ι → (ι → ℝ) → ℝ)
    (hf : ∀ ds, Measurable (fun z : Ω × (ι → ℝ) ↦ f z.1 ds z.2))
    (is ds : List ι) :
    Measurable (fun z : Ω × (ι → ℝ) ↦ cubeControl (f z.1) is ds z.2) := by
  induction is generalizing ds with
  | nil => exact (hf ds).enorm
  | cons i is ih =>
    change Measurable (fun z : Ω × (ι → ℝ) ↦
      cubeControl (f z.1) is ds (update z.2 i 0) +
        ∫⁻ t in Icc (-1:ℝ) 1, cubeControl (f z.1) is (i::ds) (update z.2 i t))
    apply Measurable.add
    · exact (ih ds).comp (measurable_fst.prodMk (measurable_coordinate_update measurable_snd measurable_const i))
    · apply Measurable.lintegral_prod_right
      exact (ih (i::ds)).comp ((measurable_fst.fst).prodMk
        (measurable_coordinate_update measurable_fst.snd measurable_snd i))

lemma cubeControl_measurable_at (f : Ω → List ι → (ι → ℝ) → ℝ)
    (hf : ∀ ds, Measurable (fun z : Ω × (ι → ℝ) ↦ f z.1 ds z.2))
    (is ds : List ι) (x : ι → ℝ) :
    Measurable (fun a ↦ cubeControl (f a) is ds x) :=
  (cubeControl_measurable f hf is ds).comp (measurable_id.prodMk measurable_const)

lemma cubeControl_lintegral_le (f : Ω → List ι → (ι → ℝ) → ℝ)
    (hf : ∀ ds, Measurable (fun z : Ω × (ι → ℝ) ↦ f z.1 ds z.2))
    (μ : Measure Ω) [SFinite μ] (d : ℕ) (C : ℝ≥0∞)
    (hb : ∀ ds, ds.length ≤ d → ∀ x, InUnitCube x →
      (∫⁻ a, ‖f a ds x‖ₑ ∂μ) ≤ C)
    (is ds : List ι) (hlen : ds.length + is.length ≤ d)
    (x : ι → ℝ) (hx : InUnitCube x) :
    (∫⁻ a, cubeControl (f a) is ds x ∂μ) ≤ 3^is.length * C := by
  induction is generalizing ds x with
  | nil => simpa [cubeControl] using hb ds (by simpa using hlen) x hx
  | cons i is ih =>
    have hm (ds' : List ι) (y : ι → ℝ) :
        Measurable (fun a ↦ cubeControl (f a) is ds' y) :=
      (cubeControl_measurable f hf is ds').comp (measurable_id.prodMk measurable_const)
    have hj : Measurable (fun z : Ω × ℝ ↦
        cubeControl (f z.1) is (i::ds) (update x i z.2)) :=
      (cubeControl_measurable f hf is (i::ds)).comp
        (measurable_fst.prodMk (measurable_coordinate_update measurable_const measurable_snd i))
    simp only [cubeControl]
    rw [lintegral_add_left (hm ds _), lintegral_lintegral_swap hj.aemeasurable]
    calc
      _ ≤ 3^is.length*C + ∫⁻ t in Icc (-1:ℝ) 1, 3^is.length*C := by
        apply add_le_add (ih ds (by simp_all only [List.length_cons]; omega) _
          (inUnitCube_update hx i (by norm_num)))
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
        exact ih (i::ds) (by simp_all only [List.length_cons]; omega) _
          (inUnitCube_update hx i (abs_le.mpr ht))
      _ = _ := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
          List.length_cons, pow_succ]
        norm_num
        ring

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CubeGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Set
open scoped ENNReal ContDiff
noncomputable section

lemma inUnitCube_of_source_ball {x : _root_.OAI.Yau.Jets.Coord} (hx : sourceEuclideanNorm x ≤ 1) :
    InUnitCube x := by
  intro j
  exact (norm_le_pi_norm x j).trans ((norm_le_sourceEuclideanNorm x).trans hx)

lemma source_two_ball_of_inUnitCube {x : _root_.OAI.Yau.Jets.Coord} (hx : InUnitCube x) :
    sourceEuclideanNorm x ≤ 2 := by
  have hh : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hx
  exact (sourceEuclideanNorm_le x).trans (by linarith)

lemma sourceEuclideanNorm_le_two_sum (x : _root_.OAI.Yau.Jets.Coord) :
    sourceEuclideanNorm x ≤ 2 * ∑ j, |x j| := by
  apply (sourceEuclideanNorm_le x).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))).mpr
  intro j
  exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (x i)) (Finset.mem_univ j)

lemma partial_enorm_le_control (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (ds : List (Fin 4)) (x : _root_.OAI.Yau.Jets.Coord) (hx : InUnitCube x) :
    ‖partialJet f ds x‖ₑ ≤ partialCubeControl f ds := by
  apply enorm_le_cubeControl_zero (partialJet f)
    (fun ds ↦ (partialJet_smooth f hf ds).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun _ _ _ ↦ rfl) [0,1,2,3] ds _ x hx
  intro i
  fin_cases i <;> simp

lemma gradient_enorm_le_cube_control (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : _root_.OAI.Yau.Jets.Coord) (hx : sourceEuclideanNorm x ≤ 1) :
    ENNReal.ofReal (sourceEuclideanNorm (fun j ↦ fderiv ℝ f x (Pi.single j 1))) ≤
      2 * ∑ j : Fin 4, partialCubeControl f [j] := by
  calc
    _ ≤ ENNReal.ofReal (2 * ∑ j : Fin 4, |fderiv ℝ f x (Pi.single j 1)|) :=
      ENNReal.ofReal_le_ofReal (sourceEuclideanNorm_le_two_sum _)
    _ = 2 * ∑ j : Fin 4, ‖partialJet f [j] x‖ₑ := by
      rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_sum_of_nonneg
        (fun _ _ ↦ abs_nonneg _)]
      simp [partialJet,← Real.norm_eq_abs]
    _ ≤ _ := mul_le_mul' le_rfl (Finset.sum_le_sum (fun j _ ↦
      partial_enorm_le_control f hf [j] x (inUnitCube_of_source_ball hx)))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FirstMomentFromSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma lintegral_enorm_le_of_square {f : Ω → ℝ} (hf : MemLp f 2 μ)
    {C : ℝ} (hC : (∫ a, (f a)^2 ∂μ) ≤ C) :
    (∫⁻ a, ‖f a‖ₑ ∂μ) ≤ ENNReal.ofReal (C+1) := by
  have hi : Integrable f μ := hf.integrable (by norm_num)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ a, ‖f a‖ ∂μ) ≤ ∫ a, (f a)^2+1 ∂μ := by
      apply integral_mono hi.norm (hf.integrable_sq.add (integrable_const 1))
      intro a
      change |f a| ≤ (f a)^2+1
      nlinarith [sq_nonneg (|f a|-1),sq_abs (f a)]
    _ = (∫ a, (f a)^2 ∂μ)+1 := by rw [integral_add hf.integrable_sq (integrable_const 1)]; simp
    _ ≤ C+1 := by linarith

end Yau.Analysis

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

lemma rescaledSeed_smooth (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (N s sigma : ℝ) (x : _root_.OAI.Yau.Jets.Coord) :
    ContDiff ℝ ∞ (rescaledSeed S0 T0 S N s sigma x) := by
  rw [rescaledSeed_representation]
  apply contDiff_const.mul
  have hn : ContDiff ℝ ∞ (rescaledSeedNormalizer S (x,s⁻¹)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_const.mul (fderiv ℝ S x).contDiff).exp)
  exact Complex.reCLM.contDiff.comp (hn.mul (waveExp_contDiff
    ((rescaledSeedPhase_smooth S0 T0 hS0 hT0).comp
      (contDiff_const.prodMk contDiff_id)) N))

lemma rescaledGaussianField_derivative_moment (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (N s sigma : ℝ) (x y : _root_.OAI.Yau.Jets.Coord) (k : ℕ) (v : Fin k → _root_.OAI.Yau.Jets.Coord) :
    ∫ a, (iteratedFDeriv ℝ k (rescaledGaussianField V S0 T0 S N s sigma x a) y v)^2
      ∂gaussianPairs =
      (iteratedFDeriv ℝ k (rescaledSeed S0 T0 S N s sigma x) y v)^2 +
        ∑ i, ‖iteratedFDeriv ℝ k (normalizedRescaling (V i) S N s sigma x) y v‖^2 := by
  have he (a : ι × Fin 2 → ℝ) : rescaledGaussianField V S0 T0 S N s sigma x a =
      fun z ↦ rescaledSeed S0 T0 S N s sigma x z +
        gaussianWaveField (fun i ↦ normalizedRescaling (V i) S N s sigma x) a z := by
    ext z
    exact rescaledGaussianField_decomposition _ _ _ _ _ _ _ _ _ _
  simp_rw [he]
  exact seeded_gaussian_derivative_moment _ _
    (fun i ↦ normalizedRescaling_smooth _ (hV i) _ _ _ _ _)
    (rescaledSeed_smooth _ _ _ hS0 hT0 _ _ _ _) _ _ _

lemma rescaledGaussianField_derivative_memLp (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (N s sigma : ℝ) (x y : _root_.OAI.Yau.Jets.Coord) (k : ℕ) (v : Fin k → _root_.OAI.Yau.Jets.Coord) :
    MemLp (fun a ↦ iteratedFDeriv ℝ k
      (rescaledGaussianField V S0 T0 S N s sigma x a) y v) 2 gaussianPairs := by
  have he (a : ι × Fin 2 → ℝ) : rescaledGaussianField V S0 T0 S N s sigma x a =
      fun z ↦ rescaledSeed S0 T0 S N s sigma x z +
        gaussianWaveField (fun i ↦ normalizedRescaling (V i) S N s sigma x) a z := by
    ext z
    exact rescaledGaussianField_decomposition _ _ _ _ _ _ _ _ _ _
  simp_rw [he]
  exact seeded_gaussian_derivative_memLp _ _
    (fun i ↦ normalizedRescaling_smooth _ (hV i) _ _ _ _ _)
    (rescaledSeed_smooth _ _ _ hS0 hT0 _ _ _ _) _ _ _

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianGradientSupremum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

lemma pairVectorSection_apply (M : Fin 4 → C(X,ℝ)) (Z : Fin 4 → ι → C(X,ℂ))
    (a : ι × Fin 2 → ℝ) (x : X) (j : Fin 4) :
    pairVectorSection M Z a x j = M j x+pairLinearSum (fun i ↦ Z j i x) a := by
  classical
  simp only [pairVectorSection,ContinuousMap.add_apply,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,PiLp.add_apply,
    vectorMeanSection,ContinuousMap.coe_mk,pairLinearSum,vectorCoeffSection]
  congr 1
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp [smul_eq_mul,mul_comm]

lemma pairVectorSection_continuous (M : Fin 4 → C(X,ℝ)) (Z : Fin 4 → ι → C(X,ℂ)) :
    Continuous (pairVectorSection M Z) := by
  unfold pairVectorSection
  exact continuous_const.add (continuous_finsetSum _ (fun p _ ↦
    (continuous_apply p).smul continuous_const))

variable [CompactSpace X]

lemma pairVectorSection_integrable (M : Fin 4 → C(X,ℝ)) (Z : Fin 4 → ι → C(X,ℂ)) :
    Integrable (pairVectorSection M Z) gaussianPairs := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  unfold pairVectorSection
  apply (integrable_const (μ := gaussianPairs (ι := ι)) (vectorMeanSection M)).add
  apply integrable_finsetSum
  intro p _
  exact (integrable_eval (μ := fun _ : ι × Fin 2 ↦ gaussianReal 0 1)
    (i := p) IsGaussian.integrable_id).smul_const _

variable (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ)
  (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
  (hV : ∀ i, ContDiff ℝ ∞ (V i))
  (hs : ContDiff ℝ ∞ seed)
  (K : Set _root_.OAI.Yau.Jets.Coord)
  [CompactSpace K]

omit [CompactSpace K] in
lemma gaussianGradientSection_apply (a : ι × Fin 2 → ℝ) (x : K) (j : Fin 4) :
    gaussianGradientSection V seed hV hs K a x j =
      fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x (Pi.single j 1) := by
  rw [gaussianGradientSection,pairVectorSection_apply]
  have hh := seeded_gaussian_iterated_apply V seed hV hs a 1 x (fun _ ↦ Pi.single j 1)
  simpa only [derivativeSection,ContinuousMap.coe_mk,iteratedFDeriv_one_apply] using hh.symm

lemma gaussianGradientSup_continuous : Continuous (gaussianGradientSup V seed hV hs K) :=
  (pairVectorSection_continuous _ _).norm

lemma gaussianGradientSup_integrable : Integrable (gaussianGradientSup V seed hV hs K) gaussianPairs :=
  (pairVectorSection_integrable _ _).norm

lemma gaussianGradientSup_le_iff (a : ι × Fin 2 → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    gaussianGradientSup V seed hV hs K a ≤ C ↔
      ∀ x ∈ K, sourceEuclideanNorm (fun j ↦
        fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x (Pi.single j 1)) ≤ C := by
  unfold gaussianGradientSup
  rw [ContinuousMap.norm_le _ hC]
  have he (x : K) : ‖gaussianGradientSection V seed hV hs K a x‖ =
      sourceEuclideanNorm (fun j ↦
        fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z) x (Pi.single j 1)) := by
    rw [EuclideanSpace.norm_eq]
    simp only [gaussianGradientSection_apply,Real.norm_eq_abs,sq_abs,sourceEuclideanNorm]
  simp_rw [he]
  exact Subtype.forall

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianCubeExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Yau.Probability MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussian_partial_control_expectation (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) {C : ℝ}
    (hb : ∀ x : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm x ≤ 2 → ∀ k : ℕ, k ≤ 5 →
      ∀ dirs : Fin k → _root_.OAI.Yau.Jets.Coord, ‖dirs‖ ≤ 1 →
        (∫ a, (iteratedFDeriv ℝ k (fun z ↦ seed z+gaussianWaveField V a z) x dirs)^2
          ∂gaussianPairs) ≤ C) (j : Fin 4) :
    (∫⁻ a, partialCubeControl (fun z ↦ seed z+gaussianWaveField V a z) [j]
      ∂gaussianPairs) ≤ 81 * ENNReal.ofReal (C+1) := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; (first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  have hF (a : ι × Fin 2 → ℝ) := hs.add (gaussianWaveField_contDiff V a hV)
  have hm (ds : List (Fin 4)) := (seeded_partial_joint_continuous V seed hV hs ds).measurable
  have hbound (ds : List (Fin 4)) (hd : ds.length ≤ 5) (x : _root_.OAI.Yau.Jets.Coord) (hx : InUnitCube x) :
      (∫⁻ a, ‖partialJet (fun z ↦ seed z+gaussianWaveField V a z) ds x‖ₑ ∂gaussianPairs) ≤
        ENNReal.ofReal (C+1) := by
    simp_rw [partialJet_eq_iterated _ (hF _)]
    exact lintegral_enorm_le_of_square
      (seeded_gaussian_derivative_memLp V seed hV hs _ _ _)
      (hb x (source_two_ball_of_inUnitCube hx) _ hd _ (partialDirs_norm_le_one ds))
  have hh := cubeControl_lintegral_le (fun a ↦ partialJet (fun z ↦ seed z+gaussianWaveField V a z))
      hm gaussianPairs 5 (ENNReal.ofReal (C+1)) hbound [0,1,2,3] [j] (by norm_num)
      0 (by intro i; norm_num)
  norm_num only [List.length_cons,List.length_nil] at hh
  exact hh

lemma gaussian_gradient_sup_le_control (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (K : Set _root_.OAI.Yau.Jets.Coord) [CompactSpace K] (hK : ∀ x ∈ K, sourceEuclideanNorm x ≤ 1)
    (a : ι × Fin 2 → ℝ) :
    ENNReal.ofReal (gaussianGradientSup V seed hV hs K a) ≤
      2 * ∑ j : Fin 4, partialCubeControl (fun z ↦ seed z+gaussianWaveField V a z) [j] := by
  rw [gaussianGradientSup,ofReal_norm,ContinuousMap.enorm_eq_iSup_enorm]
  apply iSup_le
  intro x
  have he : ‖gaussianGradientSection V seed hV hs K a x‖ =
      sourceEuclideanNorm (fun j ↦ fderiv ℝ (fun z ↦ seed z+gaussianWaveField V a z)
        x (Pi.single j 1)) := by
    rw [EuclideanSpace.norm_eq]
    simp only [gaussianGradientSection_apply,Real.norm_eq_abs,sq_abs,sourceEuclideanNorm]
  rw [← ofReal_norm,he]
  exact gradient_enorm_le_cube_control _ (hs.add (gaussianWaveField_contDiff V a hV))
    x (hK x x.property)

lemma gaussian_control_measurable (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) (ds : List (Fin 4)) :
    Measurable (fun a ↦ partialCubeControl (fun z ↦ seed z+gaussianWaveField V a z) ds) := by
  unfold partialCubeControl
  exact cubeControl_measurable_at
    (fun a ↦ partialJet (fun z ↦ seed z+gaussianWaveField V a z))
    (fun ds ↦ (seeded_partial_joint_continuous V seed hV hs ds).measurable)
    [0,1,2,3] ds 0

 theorem gaussian_gradient_expectation_of_moments (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm x ≤ 2 → ∀ k : ℕ, k ≤ 5 →
      ∀ dirs : Fin k → _root_.OAI.Yau.Jets.Coord, ‖dirs‖ ≤ 1 →
        (∫ a, (iteratedFDeriv ℝ k (fun z ↦ seed z+gaussianWaveField V a z) x dirs)^2
          ∂gaussianPairs) ≤ C)
    (K : Set _root_.OAI.Yau.Jets.Coord) [CompactSpace K] (hK : ∀ x ∈ K, sourceEuclideanNorm x ≤ 1) :
    (∫ a, gaussianGradientSup V seed hV hs K a ∂gaussianPairs) ≤ 648*(C+1) := by
  have hm (j : Fin 4) : Measurable (fun a ↦
      partialCubeControl (fun z ↦ seed z+gaussianWaveField V a z) [j]) :=
    gaussian_control_measurable V seed hV hs [j]
  have hh : (∫⁻ a, ENNReal.ofReal (gaussianGradientSup V seed hV hs K a) ∂gaussianPairs) ≤
      ENNReal.ofReal (648*(C+1)) := by
    calc
      _ ≤ ∫⁻ a, 2*∑ j : Fin 4, partialCubeControl
          (fun z ↦ seed z+gaussianWaveField V a z) [j] ∂gaussianPairs :=
        lintegral_mono (gaussian_gradient_sup_le_control V seed hV hs K hK)
      _ = 2 * ∑ j : Fin 4, ∫⁻ a, partialCubeControl
          (fun z ↦ seed z+gaussianWaveField V a z) [j] ∂gaussianPairs := by
        rw [lintegral_const_mul' _ _ (by norm_num),lintegral_finsetSum _ (fun j _ ↦ hm j)]
      _ ≤ 2 * ∑ j : Fin 4, 81*ENNReal.ofReal (C+1) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum (fun j _ ↦
          gaussian_partial_control_expectation V seed hV hs hb j))
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num <;> ring
  rw [← ofReal_integral_eq_lintegral_ofReal
    (gaussianGradientSup_integrable V seed hV hs K)
    (Filter.Eventually.of_forall (fun a ↦ norm_nonneg _))] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledSeedDecay
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

theorem rescaled_seed_decay (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ x ∈ Q, S0 x+δ ≤ S x)
    (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ s : ℝ, 1 ≤ s → ∀ v : _root_.OAI.Yau.Jets.Coord, ‖v‖ ≤ R →
        ‖iteratedFDeriv ℝ k
          (rescaledSeed S0 T0 S n s (a.latticeSigma hUD n x) x) v‖ ≤ ε := by
  obtain ⟨c,hc,C,hC,hsigma⟩ := a.lattice_sigma_comparison hUD hU hUb hQ hQU
  obtain ⟨B,hB,hseed⟩ := rescaledSeed_derivative_bound S0 T0 S hS0 hT0 hS hQ R k
  obtain ⟨L,hL,hshift⟩ := compact_rescaled_envelope_bound S0 hS0 hQ R hR
  have hdecay : Tendsto (fun n : ℕ ↦ (B*Real.exp L/c)*
      ((n:ℝ)^k*Real.exp (-δ*(n:ℝ)))) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) δ hδ).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop)
    simpa only [Function.comp_def,Real.rpow_natCast,mul_zero] using ht.const_mul (B*Real.exp L/c)
  filter_upwards [hsigma,hdecay.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)]
    with n hn hsmall hnpos
  obtain ⟨hfin,hσ⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx s hs v hv
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hn0 : (0:ℝ) < n := by exact_mod_cast hnpos
  have hσ0 : 0 < a.latticeSigma hUD n x :=
    lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) (hσ x hx).1
  have he : Real.exp ((n:ℝ)*S0 (x+((n:ℝ)*s)⁻¹ • v)) ≤
      Real.exp ((n:ℝ)*S x)*Real.exp (-δ*(n:ℝ))*Real.exp L := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := (le_abs_self _).trans (hshift n s hnR hs x hx v hv)
    have hg := mul_le_mul_of_nonneg_left (hgap x hx) hn0.le
    nlinarith
  have hσ' := mul_le_mul_of_nonneg_left (hσ x hx).1
    (by positivity : 0 ≤ (B*Real.exp L/c)*((n:ℝ)^k*Real.exp (-δ*(n:ℝ))))
  apply (hseed n s _ hnR hs hσ0 x hx v hv).trans
  apply le_trans _ hsmall.le
  apply (div_le_iff₀ hσ0).mpr
  calc
    _ ≤ B*(n:ℝ)^k*(Real.exp ((n:ℝ)*S x)*Real.exp (-δ*(n:ℝ))*Real.exp L) := by gcongr
    _ = ((B*Real.exp L/c)*((n:ℝ)^k*Real.exp (-δ*(n:ℝ))))*
        (c*Real.exp ((n:ℝ)*S x)) := by field_simp
    _ ≤ _ := hσ'

end LocalCompactWaveData
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

theorem sign_scale_seed_decay (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U)
    (hS : ContDiff ℝ ∞ S) (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ x ∈ Q, S0 x+δ ≤ S x)
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
      ∀ x ∈ Q, ∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ 2 → ∀ k : Fin (d+1),
        ‖iteratedFDeriv ℝ k.val
          (rescaledSeed S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x) v‖ ≤ ε := by
  have hall := Filter.eventually_all.mpr (fun k : Fin (d+1) ↦
    a.rescaled_seed_decay hUD hU hUb hQ hQU hS S0 T0 hS0 hT0 δ hδ hgap 2 (by norm_num) k.val ε hε)
  filter_upwards [hall] with n hn
  obtain ⟨hfin,_⟩ := hn ⟨0,by omega⟩
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v hv k
  obtain ⟨hfin',hb⟩ := hn k
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  exact hb x hx _ (by linarith [a.source_sign_scale_lower x (hUD (hQU hx))]) v
    ((norm_le_sourceEuclideanNorm v).trans hv)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledGradientExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory Set Filter
open scoped ContDiff Topology
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma rescaled_gradient_supremum_expectation (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (N s sigma : ℝ) (x : _root_.OAI.Yau.Jets.Coord) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ 2 → ∀ k : ℕ, k ≤ 5 →
      ∀ dirs : Fin k → _root_.OAI.Yau.Jets.Coord, ‖dirs‖ ≤ 1 →
        (∫ coeff, (iteratedFDeriv ℝ k
          (rescaledGaussianField V S0 T0 S N s sigma x coeff) v dirs)^2 ∂gaussianPairs) ≤ B) :
    ∃ G : (ι × Fin 2 → ℝ) → ℝ,
      Continuous G ∧ Integrable G gaussianPairs ∧ (∀ coeff, 0 ≤ G coeff) ∧
      (∫ coeff, G coeff ∂gaussianPairs) ≤ 648*(B+1) ∧
      ∀ coeff C, 0 ≤ C →
        (G coeff ≤ C ↔ ∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ 1 →
          sourceEuclideanNorm (fun j ↦ fderiv ℝ
            (rescaledGaussianField V S0 T0 S N s sigma x coeff) v (Pi.single j 1)) ≤ C) := by
  let K := {v : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm v ≤ 1}
  let : CompactSpace K := isCompact_iff_compactSpace.mp (sourceEuclideanBall_compact 1)
  let A := fun i ↦ normalizedRescaling (V i) S N s sigma x
  let seed := rescaledSeed S0 T0 S N s sigma x
  have hA (i : ι) : ContDiff ℝ ∞ (A i) := normalizedRescaling_smooth _ (hV i) _ _ _ _ _
  have hs : ContDiff ℝ ∞ seed := rescaledSeed_smooth _ _ _ hS0 hT0 _ _ _ _
  have he (coeff : ι × Fin 2 → ℝ) : rescaledGaussianField V S0 T0 S N s sigma x coeff =
      fun z ↦ seed z+gaussianWaveField A coeff z := by
    ext z
    exact rescaledGaussianField_decomposition _ _ _ _ _ _ _ _ _ _
  have hb' : ∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ 2 → ∀ k : ℕ, k ≤ 5 →
      ∀ dirs : Fin k → _root_.OAI.Yau.Jets.Coord, ‖dirs‖ ≤ 1 →
        (∫ coeff, (iteratedFDeriv ℝ k
          (fun z ↦ seed z+gaussianWaveField A coeff z) v dirs)^2 ∂gaussianPairs) ≤ B := by
    simpa only [he] using hb
  refine ⟨gaussianGradientSup A seed hA hs K,
    gaussianGradientSup_continuous _ _ _ _ _,gaussianGradientSup_integrable _ _ _ _ _,
    fun coeff ↦ norm_nonneg _,
    gaussian_gradient_expectation_of_moments A seed hA hs hB hb' K (fun _ hx ↦ hx),?_⟩
  intro coeff C hC
  rw [he coeff]
  exact gaussianGradientSup_le_iff A seed hA hs K coeff hC

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RescaledSignTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma rescaledGaussianField_sign (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N s sigma : ℝ) (x : _root_.OAI.Yau.Jets.Coord) (coeff : ι × Fin 2 → ℝ) (v : _root_.OAI.Yau.Jets.Coord)
    (hsigma : 0 < sigma) :
    (0 < rescaledGaussianField V S0 T0 S N s sigma x coeff v ↔
      0 < oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v)+
        gaussianWaveField V coeff (x+(N*s)⁻¹ • v)) ∧
    (rescaledGaussianField V S0 T0 S N s sigma x coeff v < 0 ↔
      oscillatorySeed S0 T0 N (x+(N*s)⁻¹ • v)+
        gaussianWaveField V coeff (x+(N*s)⁻¹ • v) < 0) := by
  have hden : 0 < sigma*Real.exp (fderiv ℝ S x v/s) := mul_pos hsigma (Real.exp_pos _)
  constructor
  · exact div_pos_iff_of_pos_right hden
  · change _ / _ < 0 ↔ _ < 0
    rw [div_lt_iff₀ hden,zero_mul]

lemma rescaled_sign_subballs_transfer (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (S0 T0 S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N s sigma : ℝ) (x : _root_.OAI.Yau.Jets.Coord) (coeff : ι × Fin 2 → ℝ)
    (hscale : 0 < N*s) (hsigma : 0 < sigma) (tau r : ℝ) (j : Fin 4)
    (hpos : ∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ r →
      0 < rescaledGaussianField V S0 T0 S N s sigma x coeff v)
    (hneg : ∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
      rescaledGaussianField V S0 T0 S N s sigma x coeff v < 0) :
    (∀ y : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (y-x) ≤ r/(N*s) →
      0 < oscillatorySeed S0 T0 N y+gaussianWaveField V coeff y) ∧
    (∀ y : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (y-(x+(N*s)⁻¹ • (tau • Pi.single j 1))) ≤ r/(N*s) →
      oscillatorySeed S0 T0 N y+gaussianWaveField V coeff y < 0) := by
  have he (y : _root_.OAI.Yau.Jets.Coord) : x+(N*s)⁻¹ • ((N*s) • (y-x)) = y := by
    rw [smul_smul,inv_mul_cancel₀ hscale.ne',one_smul,add_sub_cancel]
  constructor
  · intro y hy
    have hv : sourceEuclideanNorm ((N*s) • (y-x)) ≤ r := by
      rw [sourceEuclideanNorm_smul,abs_of_pos hscale]
      have hh := (le_div_iff₀ hscale).mp hy
      nlinarith
    have hh := (rescaledGaussianField_sign V S0 T0 S N s sigma x coeff _ hsigma).1.mp (hpos _ hv)
    simpa only [he] using hh
  · intro y hy
    have heq : (N*s) • (y-x)-tau • Pi.single j (1:ℝ) =
        (N*s) • (y-(x+(N*s)⁻¹ • (tau • Pi.single j 1))) := by
      have hid : (N*s)*((N*s)⁻¹*tau) = tau := by rw [← mul_assoc,mul_inv_cancel₀ hscale.ne',one_mul]
      simp only [smul_sub,smul_add,smul_smul,hid]
      abel
    have hv : sourceEuclideanNorm ((N*s) • (y-x)-tau • Pi.single j (1:ℝ)) ≤ r := by
      rw [heq,sourceEuclideanNorm_smul,abs_of_pos hscale]
      have hh := (le_div_iff₀ hscale).mp hy
      nlinarith
    have hh := (rescaledGaussianField_sign V S0 T0 S N s sigma x coeff _ hsigma).2.mp (hneg _ hv)
    simpa only [he] using hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SignEventMarkov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

lemma event_inter_gradient_bound {A : Set Ω} {G : Ω → ℝ}
    (hG : Integrable G μ) (hG0 : ∀ x, 0 ≤ G x) {L : ℝ} (hL : 0 < L) :
    μ.real A - (∫ x, G x ∂μ)/L ≤ μ.real (A ∩ {x | G x ≤ L}) := by
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hG0) hG L
  have htail : μ.real {x | L ≤ G x} ≤ (∫ x, G x ∂μ)/L := by
    apply (le_div_iff₀ hL).mpr
    linarith
  have hcover : A ⊆ (A ∩ {x | G x ≤ L}) ∪ {x | L ≤ G x} := by
    intro x hx
    by_cases hh : G x ≤ L
    · exact Or.inl ⟨hx,hh⟩
    · exact Or.inr (le_of_lt (lt_of_not_ge hh))
  have hmeasure := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le (μ := μ) _ _)
  linarith

lemma event_inter_gradient_half {A : Set Ω} {G : Ω → ℝ}
    (hG : Integrable G μ) (hG0 : ∀ x, 0 ≤ G x) {p L : ℝ} (hL : 0 < L)
    (hA : p ≤ μ.real A) (hmean : 2*(∫ x, G x ∂μ) ≤ p*L) :
    p/2 ≤ μ.real (A ∩ {x | G x ≤ L}) := by
  have h := event_inter_gradient_bound (A := A) hG hG0 hL
  have hratio : (∫ x, G x ∂μ)/L ≤ p/2 := by
    apply (div_le_iff₀ hL).mpr
    linarith
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_StrictSignSubballs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma choose_sign_subball_radius {tau L : ℝ} (ht : 0 < tau) (ht1 : tau < 1) (hL : 0 ≤ L) :
    ∃ r > 0, r < tau/4 ∧ r < (1-tau)/2 ∧ 4*L*r < 1 := by
  let r := min (tau/8) (min ((1-tau)/4) (1/(16*(L+1))))
  have hr : 0 < r := by dsimp [r] <;> positivity
  have h1 : r ≤ tau/8 := min_le_left _ _
  have h2 : r ≤ (1-tau)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : r ≤ 1/(16*(L+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hprod : 16*(L+1)*r ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 16*(L+1))).mp h3
    nlinarith
  refine ⟨r,hr,by linarith,by linarith,?_⟩
  nlinarith [mul_nonneg hL hr.le]

lemma strict_sign_subballs (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    {tau r L : ℝ} (ht : 0 ≤ tau) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (htr : tau+r ≤ 1) (hsmall : 4*L*r < 1) (j : Fin 4)
    (hpos : 1 ≤ f 0) (hneg : f (tau • Pi.single j 1) ≤ -1)
    (hgrad : ∀ x : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm x ≤ 1 →
      sourceEuclideanNorm (fun i ↦ fderiv ℝ f x (Pi.single i 1)) ≤ L) :
    (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ r → sourceEuclideanNorm v ≤ 1 ∧ 0 < f v) ∧
    (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
      sourceEuclideanNorm v ≤ 1 ∧ f v < 0) := by
  have hdiff : ∀ x ∈ {x : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm x ≤ 1}, DifferentiableAt ℝ f x :=
    fun x _ ↦ hf.differentiable (by simp) x
  have hb : ∀ x ∈ {x : _root_.OAI.Yau.Jets.Coord | sourceEuclideanNorm x ≤ 1}, ‖fderiv ℝ f x‖ ≤ 4*L := by
    intro x hx
    exact (covector_norm_le_source _).trans (by linarith [hgrad x hx])
  have hc := sourceEuclideanBall_convex 1
  obtain ⟨hinside0,hinside1⟩ := source_sign_subballs_inside ht hr htr j
  constructor
  · intro v hv
    have hv1 := hinside0 v hv
    have hh := hc.norm_image_sub_le_of_norm_fderiv_le hdiff hb
      (show (0:_root_.OAI.Yau.Jets.Coord) ∈ {x | sourceEuclideanNorm x ≤ 1} by simp [sourceEuclideanNorm]) hv1
    have hnv : ‖v-(0:_root_.OAI.Yau.Jets.Coord)‖ ≤ r := by simpa using (norm_le_sourceEuclideanNorm v).trans hv
    have hb' : |f v-f 0| ≤ 4*L*r := by
      exact hh.trans (mul_le_mul_of_nonneg_left hnv (by positivity))
    refine ⟨hv1,?_⟩
    have hh' := (abs_le.mp hb').1
    linarith
  · intro v hv
    have hv1 := hinside1 v hv
    have ht1 : sourceEuclideanNorm (tau • Pi.single j (1:ℝ)) ≤ 1 := by
      rw [sourceEuclideanNorm_single,abs_of_nonneg ht]
      linarith
    have hh := hc.norm_image_sub_le_of_norm_fderiv_le hdiff hb ht1 hv1
    have hnv := (norm_le_sourceEuclideanNorm (v-tau • Pi.single j 1)).trans hv
    have hb' : |f v-f (tau • Pi.single j 1)| ≤ 4*L*r :=
      hh.trans (mul_le_mul_of_nonneg_left hnv (by positivity))
    refine ⟨hv1,?_⟩
    have hh' := (abs_le.mp hb').2
    linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FixedDomainLatticeDerivativeMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_derivative_second_moments_fixed_domain
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) (d : ℕ) :
    ∃ C > 0, ∀ (w S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → d ≤ k0 →
      ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ 2 → ∀ k : ℕ, k ≤ d →
        ∀ dirs : Fin k → _root_.OAI.Yau.Jets.Coord, ‖dirs‖ ≤ 1 →
        let F := rescaledGaussianField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
          S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
        MemLp (fun coeff ↦ iteratedFDeriv ℝ k (F coeff) v dirs) 2 gaussianPairs ∧
        (∫ coeff, (iteratedFDeriv ℝ k (F coeff) v dirs)^2 ∂gaussianPairs) ≤ C := by
  obtain ⟨C,hC,henergy⟩ := lattice_actual_derivative_energy_fixed_domain g hH hg hp d
  refine ⟨1+C,by positivity,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hS0 hT0 hd gamma hgamma hgap
  filter_upwards [henergy w S D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hd,
    a.sign_scale_seed_decay hUD hU hUb hQ hQU hS S0 T0 hS0 hT0 gamma hgamma hgap d 1 (by norm_num),
    a.estimates] with n he hs hest
  obtain ⟨hfin,he⟩ := he
  obtain ⟨hfin',hs⟩ := hs
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx v hv k hk dirs hdirs
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
  refine ⟨rescaledGaussianField_derivative_memLp V hV _ _ _ hS0 hT0 _ _ _ _ _ _ _,?_⟩
  rw [rescaledGaussianField_derivative_moment V hV _ _ _ hS0 hT0]
  have hseed := hs x hx v hv (⟨k,by omega⟩ : Fin (d+1))
  have hseed' := (iteratedFDeriv ℝ k
    (rescaledSeed S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x) v).unit_le_opNorm hdirs
  have hmean := pow_le_pow_left₀ (norm_nonneg _) (hseed'.trans hseed) 2
  simp only [Real.norm_eq_abs,sq_abs,one_pow] at hmean
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (SourceGrid U n × Fin 3))) ↦
    pow_le_pow_left₀ (norm_nonneg _)
      ((iteratedFDeriv ℝ k (normalizedRescaling (V i) S n (sourceSignScale g S x)
        (a.latticeSigma hUD n x) x) v).unit_le_opNorm hdirs) 2)
  have hbound := he x hx v ((norm_le_sourceEuclideanNorm v).trans hv) k hk
  change (∑ i, ‖iteratedFDeriv ℝ k (normalizedRescaling (V i) S n (sourceSignScale g S x)
    (a.latticeSigma hUD n x) x) v‖^2) ≤ C at hbound
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FixedDomainLatticeGradientExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_gradient_expectation_fixed_domain
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ C > 0, ∀ (w S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
      (a : LocalCompactWaveData g w S D m J K k0), IsCompact D → D ⊆ H → ∀ (hUD : U ⊆ D),
      U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
      ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → 5 ≤ k0 →
      ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
      ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
        ∀ x ∈ Q, ∃ G : ((SourceGrid U n × Fin 3) × Fin 2 → ℝ) → ℝ,
          Continuous G ∧ Integrable G gaussianPairs ∧ (∀ coeff, 0 ≤ G coeff) ∧
          (∫ coeff, G coeff ∂gaussianPairs) ≤ C ∧
          ∀ coeff L, 0 ≤ L →
            (G coeff ≤ L ↔ ∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ 1 →
              sourceEuclideanNorm (fun j ↦ fderiv ℝ (rescaledGaussianField
                (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
                S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x coeff)
                  v (Pi.single j 1)) ≤ L) := by
  obtain ⟨B,hB,hmom⟩ := lattice_derivative_second_moments_fixed_domain g hH hg hp 5
  refine ⟨648*(B+1),by positivity,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hS0 hT0 hd gamma hgamma hgap
  filter_upwards [hmom w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
    hS hS0 hT0 hd gamma hgamma hgap,a.estimates] with n hn hest
  obtain ⟨hfin,hn⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
  exact rescaled_gradient_supremum_expectation V hV S0 T0 S hS0 hT0
    n (sourceSignScale g S x) (a.latticeSigma hUD n x) x hB.le
    (fun v hv k hk dirs hd ↦ (hn x hx v hv k hk dirs hd).2)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_SignSubballProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets MeasureTheory Set
open scoped ContDiff ENNReal
noncomputable section

lemma positive_real_probability_floor {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ ENNReal.ofReal q ≤ p := by
  let b := min p 1
  have hb : 0 < b := lt_min hp (by norm_num)
  have ht : b ≠ ⊤ := ne_of_lt ((min_le_right p 1).trans_lt (by norm_num))
  refine ⟨b.toReal,ENNReal.toReal_pos hb.ne' ht,?_,?_⟩
  · have hh := ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (min_le_right p 1)
    simpa using hh
  · rw [ENNReal.ofReal_toReal ht]
    exact min_le_left p 1

lemma sign_subball_constants {tau p C : ℝ} (ht : 0 < tau) (ht1 : tau < 1)
    (hp : 0 < p) (hC : 0 ≤ C) :
    ∃ L > 0, ∃ r > 0, r < tau/4 ∧ r < (1-tau)/2 ∧ 4*L*r < 1 ∧ 2*C ≤ p*L := by
  let L := 2*C/p+1
  have hL : 0 < L := by dsimp [L] <;> positivity
  obtain ⟨r,hr,hrt,hr1,hrL⟩ := choose_sign_subball_radius ht ht1 hL.le
  refine ⟨L,hL,r,hr,hrt,hr1,hrL,?_⟩
  dsimp [L]
  have he : p*(2*C/p+1) = 2*C+p := by field_simp
  rw [he]
  linarith

lemma sign_subballs_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → _root_.OAI.Yau.Jets.Coord → ℝ)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (G : Ω → ℝ)
    (hG : Integrable G μ) (hG0 : ∀ a, 0 ≤ G a)
    {tau r p C L : ℝ} (ht : 0 ≤ tau) (hr : 0 ≤ r) (hL : 0 < L)
    (htr : tau+r ≤ 1) (hsmall : 4*L*r < 1) (hmean : (∫ a, G a ∂μ) ≤ C)
    (hCL : 2*C ≤ p*L)
    (hgrad : ∀ a, G a ≤ L → ∀ x : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm x ≤ 1 →
      sourceEuclideanNorm (fun i ↦ fderiv ℝ (F a) x (Pi.single i 1)) ≤ L)
    (j : Fin 4) (hsign : p ≤ μ.real {a | 1 ≤ F a 0 ∧ F a (tau • Pi.single j 1) ≤ -1}) :
    p/2 ≤ μ.real {a |
      (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ r → sourceEuclideanNorm v ≤ 1 ∧ 0 < F a v) ∧
      (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
        sourceEuclideanNorm v ≤ 1 ∧ F a v < 0)} := by
  have hh := event_inter_gradient_half hG hG0 hL hsign (by linarith : 2*(∫ a, G a ∂μ) ≤ p*L)
  apply hh.trans
  apply measureReal_mono
  · intro a ha
    exact strict_sign_subballs (F a) (hF a) ht hr hL.le htr hsmall j ha.1.1 ha.1.2
      (hgrad a ha.2)
  · exact measure_ne_top _ _

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FixedDomainLatticeSignSubballs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_sign_subballs_probability_fixed_domain
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ r : ℝ, 0 < r ∧
      r < tau/4 ∧ r < (1-tau)/2 ∧ ∃ p : ℝ, 0 < p ∧
      ∀ (w S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → 5 ≤ k0 →
        ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∀ x ∈ Q, ∃ j : Fin 4,
            let F := rescaledGaussianField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
              S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
            p ≤ gaussianPairs.real {coeff |
              (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm v ≤ r →
                sourceEuclideanNorm v ≤ 1 ∧ 0 < F coeff v) ∧
              (∀ v : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
                sourceEuclideanNorm v ≤ 1 ∧ F coeff v < 0)} := by
  obtain ⟨tau,ht,ht4,p,hp0,hmargin⟩ := lattice_sign_margin_probability_fixed_domain g hH hg hp
  obtain ⟨q,hq,hq1,hqp⟩ := positive_real_probability_floor hp0
  obtain ⟨C,hC,hmean⟩ := lattice_gradient_expectation_fixed_domain g hH hg hp
  obtain ⟨L,hL,r,hr,hrt,hr1,hrL,hCL⟩ := sign_subball_constants ht (by linarith) hq hC.le
  refine ⟨tau,ht,ht4,r,hr,hrt,hr1,q/2,by positivity,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hS0 hT0 hd gamma hgamma hgap
  filter_upwards [hmargin w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
    hS hS0 hT0 gamma hgamma hgap,
    hmean w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
    hS hS0 hT0 hd gamma hgamma hgap,a.estimates] with n hn hm hest
  obtain ⟨hfin,hn⟩ := hn
  obtain ⟨hfin',hm⟩ := hm
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  let : IsProbabilityMeasure (gaussianPairs (ι := SourceGrid U n × Fin 3)) := by
    unfold gaussianPairs; infer_instance
  refine ⟨hfin,?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := hn x hx
  obtain ⟨G,hGc,hGi,hG0,hGC,hGe⟩ := hm x hx
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  let F := rescaledGaussianField V S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
  have hF (coeff) : ContDiff ℝ ∞ (F coeff) := by
    have he : F coeff = fun z ↦ rescaledSeed S0 T0 S n (sourceSignScale g S x)
        (a.latticeSigma hUD n x) x z + gaussianWaveField
          (fun i ↦ normalizedRescaling (V i) S n (sourceSignScale g S x)
            (a.latticeSigma hUD n x) x) coeff z := by
      ext z
      exact rescaledGaussianField_decomposition _ _ _ _ _ _ _ _ _ _
    rw [he]
    exact (rescaledSeed_smooth _ _ _ hS0 hT0 _ _ _ _).add
      (gaussianWaveField_contDiff _ _ (fun i ↦ normalizedRescaling_smooth _ (hV i) _ _ _ _ _))
  have hqA : q ≤ gaussianPairs.real {coeff | 1 ≤ F coeff 0 ∧ F coeff (tau • Pi.single j 1) ≤ -1} := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (hqp.trans hj)
    simpa only [ENNReal.toReal_ofReal hq.le,Measure.real] using hh
  refine ⟨j,?_⟩
  exact sign_subballs_probability gaussianPairs F hF G hGi hG0 ht.le hr.le hL
    (by linarith) hrL hGC hCL (fun coeff hcoeff ↦ (hGe coeff L hL.le).mp hcoeff) j hqA

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FixedDomainLatticePhysicalSignSubballs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section

theorem lattice_physical_sign_subballs_fixed_domain_oai
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ r : ℝ, 0 < r ∧
      r < tau/4 ∧ r < (1-tau)/2 ∧ ∃ p : ℝ, 0 < p ∧
      ∀ (w S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 → 5 ≤ k0 →
        ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∀ x ∈ Q, ∃ j : Fin 4,
            let scale := (n:ℝ)*sourceSignScale g S x
            let f := fun coeff y ↦ oscillatorySeed S0 T0 n y + gaussianWaveField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff y
            let A : Set (((SourceGrid U n × Fin 3) × Fin 2) → ℝ) := {coeff |
              (∀ y : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (y-x) ≤ r/scale → 0 < f coeff y) ∧
              (∀ y : _root_.OAI.Yau.Jets.Coord, sourceEuclideanNorm (y-(x+scale⁻¹ • (tau • Pi.single j 1))) ≤ r/scale →
                f coeff y < 0)}
            0 < scale ∧ MeasurableSet A ∧ p ≤ gaussianPairs.real A := by
  obtain ⟨tau,ht,ht4,r,hr,hrt,hr1,p,hp0,hprob⟩ := lattice_sign_subballs_probability_fixed_domain g hH hg hp
  refine ⟨tau,ht,ht4,r,hr,hrt,hr1,p,hp0,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hS0 hT0 hd gamma hgamma hgap
  obtain ⟨c,hc,C,hC,hsigma⟩ := a.lattice_sigma_comparison hUD hU hUb hQ hQU
  filter_upwards [hprob w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU
    hS hS0 hT0 hd gamma hgamma hgap,hsigma,eventually_gt_atTop (0:ℕ),a.estimates] with n hn hs hn0 hest
  obtain ⟨hfin,hn⟩ := hn
  obtain ⟨hfin',hs⟩ := hs
  have heq : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  let : IsProbabilityMeasure (gaussianPairs (ι := SourceGrid U n × Fin 3)) := by
    unfold gaussianPairs; infer_instance
  refine ⟨hfin,?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := hn x hx
  have hsc : 0 < (n:ℝ)*sourceSignScale g S x := mul_pos (by exact_mod_cast hn0)
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (a.source_sign_scale_lower x (hUD (hQU hx))))
  have hsig : 0 < a.latticeSigma hUD n x :=
    (mul_pos hc (Real.exp_pos _)).trans_le (hs x hx).1
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hest (latticeFrame a.cover hUD n i.1,i.2)).1
  have hmeas := seeded_gaussian_sign_balls_measurable V (oscillatorySeed S0 T0 n)
    hV (oscillatorySeed_contDiff S0 T0 hS0 hT0 n)
    x (x+((n:ℝ)*sourceSignScale g S x)⁻¹ • (tau • Pi.single j 1))
    (r/((n:ℝ)*sourceSignScale g S x)) (r/((n:ℝ)*sourceSignScale g S x))
  refine ⟨j,hsc,hmeas,hj.trans ?_⟩
  apply measureReal_mono
  · intro coeff hcoeff
    exact rescaled_sign_subballs_transfer _ S0 T0 S n (sourceSignScale g S x)
        (a.latticeSigma hUD n x) x coeff hsc hsig tau r j
        (fun v hv ↦ (hcoeff.1 v hv).2) (fun v hv ↦ (hcoeff.2 v hv).2)
  · exact measure_ne_top _ _

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.lattice_physical_sign_subballs_fixed_domain_oai := @OAI.Yau.Geometry.lattice_physical_sign_subballs_fixed_domain_oai
