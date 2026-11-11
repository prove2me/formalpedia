-- Prove2me | solution 1 for OAI.Yau.Geometry.LocalCompactWaveData.lattice_good_event_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:40.18308+00:00
-- url     : https://prove2.me/submissions/c1f1ab4e-f542-454f-aa1a-d929498c81de

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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ237Ny000
import Definitions.Def_OAIQ237Ny001
import Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_actual_lattice_gaussian_small_ball

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GaussianCoefficientTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

lemma standard_gaussian_abs_tail {r : ℝ} (hr : 0 ≤ r) :
    gaussianReal 0 1 {x | r ≤ |x|} ≤ ENNReal.ofReal (2*Real.exp (-r^2/2)) := by
  have hu := measure_ge_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 1) r hr
    (integrable_exp_mul_gaussianReal r)
  have hl := measure_le_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 1) (-r)
    (neg_nonpos.mpr hr) (integrable_exp_mul_gaussianReal (-r))
  simp only [mgf_id_gaussianReal,zero_mul,NNReal.coe_one,one_mul,zero_add,
    ← Real.exp_add] at hu hl
  have heu : -r*r+r^2/2 = -r^2/2 := by ring
  have hel : -(-r)*(-r)+(-r)^2/2 = -r^2/2 := by ring
  rw [heu] at hu
  rw [hel] at hl
  have hu' := ENNReal.ofReal_le_ofReal hu
  have hl' := ENNReal.ofReal_le_ofReal hl
  rw [ofReal_measureReal] at hu' hl'
  have hsub : {x : ℝ | r ≤ |x|} ⊆ {x | r ≤ id x} ∪ {x | id x ≤ -r} := by
    intro x hx
    change r ≤ |x| at hx
    rcases le_abs.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (by dsimp <;> linarith)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have h := add_le_add hu' hl'
  rw [two_mul,ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  exact h

variable {ι : Type*} [Fintype ι]

lemma gaussian_pairs_coordinate_tail {r : ℝ} (hr : 0 ≤ r) (p : ι × Fin 2) :
    (gaussianPairs (ι := ι)) {a | r ≤ |a p|} ≤ ENNReal.ofReal (2*Real.exp (-r^2/2)) := by
  classical
  have hm := (measurePreserving_eval (fun _ : ι × Fin 2 ↦ gaussianReal 0 1) p).map_eq
  have h := standard_gaussian_abs_tail hr
  rw [← hm,Measure.map_apply (by fun_prop) (measurableSet_le measurable_const (by fun_prop))] at h
  exact h

theorem coefficient_event_failure {r : ℝ} (hr : 0 ≤ r) :
    (gaussianPairs (ι := ι)) (coefficientEvent (ι := ι) r)ᶜ ≤
      ENNReal.ofReal (4*(Fintype.card ι:ℝ)*Real.exp (-r^2/8)) := by
  classical
  have hsub : (coefficientEvent (ι := ι) r)ᶜ ⊆
      ⋃ p : ι × Fin 2, {a | r/2 ≤ |a p|} := by
    intro a ha
    change ¬ ∀ i, ‖(a (i,0):ℂ)+Complex.I*(a (i,1):ℂ)‖ ≤ r at ha
    push Not at ha
    obtain ⟨i,hi⟩ := ha
    have hb : ‖(a (i,0):ℂ)+Complex.I*(a (i,1):ℂ)‖ ≤ |a (i,0)|+|a (i,1)| := by
      simpa using norm_add_le (a (i,0):ℂ) (Complex.I*(a (i,1):ℂ))
    have he : r/2 ≤ |a (i,0)| ∨ r/2 ≤ |a (i,1)| := by
      by_contra hh
      push Not at hh
      linarith
    rcases he with h | h
    · exact mem_iUnion.mpr ⟨(i,0),h⟩
    · exact mem_iUnion.mpr ⟨(i,1),h⟩
  have h := (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
    (Finset.sum_le_sum (fun p _ ↦ gaussian_pairs_coordinate_tail (div_nonneg hr (by norm_num)) p)))
  have he : -(r/2)^2/2 = -r^2/8 := by ring
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [nsmul_eq_mul,Nat.cast_mul]
  norm_num
  ring

end
end Yau.Probability

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

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopeRegion
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

theorem high_envelope_fixed_compact {Ω U : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsCompact Ω)
    (hU : IsOpen U) (S S0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : Continuous S) (hS0 : Continuous S0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∃ Q : Set _root_.OAI.Yau.Jets.Coord, IsCompact Q ∧ Q ⊆ U ∧
      (∃ ε > 0, Metric.cthickening ε Q ⊆ U) ∧
      ∀ᶠ n : ℕ in atTop, highEnvelopeRegion Ω S S0 n ⊆ Q := by
  let Q := Ω ∩ {x | -d/2 ≤ S x-S0 x}
  have hQ : IsCompact Q := hΩ.inter_right (isClosed_le continuous_const (hS.sub hS0))
  have hQU : Q ⊆ U := by
    intro x hx
    by_contra hxu
    have h := hgap x hx.1 hxu
    have hx' := hx.2
    dsimp at hx'
    linarith
  refine ⟨Q,hQ,hQU,hQ.exists_cthickening_subset_open hU hQU,?_⟩
  have ht : Tendsto (fun n : ℕ ↦ -8*Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [div_eq_mul_inv,mul_assoc] using h.const_mul (-8)
  filter_upwards [ht.eventually (lt_mem_nhds (by linarith : -d/2 < (0:ℝ)))] with n hn
  intro x hx
  exact ⟨hx.1,hn.le.trans hx.2⟩

lemma high_envelope_bound {Ω : Set _root_.OAI.Yau.Jets.Coord} {S S0 : _root_.OAI.Yau.Jets.Coord → ℝ} {n : ℕ}
    (hn : 0 < n) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ highEnvelopeRegion Ω S S0 n) :
    max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) ≤
      (n:ℝ)^8*Real.exp ((n:ℝ)*S x) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hb : -8*Real.log (n:ℝ) ≤ (S x-S0 x)*(n:ℝ) :=
    (div_le_iff₀ hnR).mp hx.2
  have he : (n:ℝ)*S0 x ≤ 8*Real.log (n:ℝ)+(n:ℝ)*S x := by nlinarith
  apply max_le
  · have hp : (1:ℝ) ≤ (n:ℝ)^8 := one_le_pow₀ hn1
    nlinarith [Real.exp_pos ((n:ℝ)*S x)]
  · have h := Real.exp_le_exp.mpr he
    have hlog : Real.exp (8*Real.log (n:ℝ)) = (n:ℝ)^8 := by
      rw [show (8:ℝ)*Real.log (n:ℝ) = (8:ℕ)*Real.log (n:ℝ) by norm_num,
        Real.exp_nat_mul,Real.exp_log hnR]
    rw [Real.exp_add,hlog] at h
    exact h

lemma high_envelope_neighborhood_bound {Ω : Set _root_.OAI.Yau.Jets.Coord} {S S0 : _root_.OAI.Yau.Jets.Coord → ℝ} {n : ℕ}
    (hn : 0 < n) {x z : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ highEnvelopeRegion Ω S S0 n)
    {L : ℝ} (hL : 0 ≤ L) (hLn : L ≤ (n:ℝ))
    (hz : ‖z-x‖ ≤ ((n:ℝ)^2)⁻¹)
    (hgap : (S0 z-S z)-(S0 x-S x) ≤ L*‖z-x‖) :
    max (Real.exp ((n:ℝ)*S z)) (Real.exp ((n:ℝ)*S0 z))*Real.exp (-(n:ℝ)*S z) ≤
      Real.exp 1*(n:ℝ)^8 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hstep : L*‖z-x‖ ≤ 1/(n:ℝ) := by
    calc
      _ ≤ L*((n:ℝ)^2)⁻¹ := mul_le_mul_of_nonneg_left hz hL
      _ ≤ (n:ℝ)*((n:ℝ)^2)⁻¹ := mul_le_mul_of_nonneg_right hLn (by positivity)
      _ = _ := by field_simp
  have hdiff := hgap.trans hstep
  have hdiff' := (le_div_iff₀ hnR).mp hdiff
  have hb := (div_le_iff₀ hnR).mp hx.2
  have hpow : (1:ℝ) ≤ (n:ℝ)^8 := one_le_pow₀ hn1
  have hnum : (n:ℝ)*S0 z ≤ 1+8*Real.log (n:ℝ)+(n:ℝ)*S z := by nlinarith
  have hlog : Real.exp (8*Real.log (n:ℝ)) = (n:ℝ)^8 := by
    rw [show (8:ℝ)*Real.log (n:ℝ) = (8:ℕ)*Real.log (n:ℝ) by norm_num,
      Real.exp_nat_mul,Real.exp_log hnR]
  have hmax : max (Real.exp ((n:ℝ)*S z)) (Real.exp ((n:ℝ)*S0 z)) ≤
      (Real.exp 1*(n:ℝ)^8)*Real.exp ((n:ℝ)*S z) := by
    apply max_le
    · have he1 : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp_iff.mpr zero_le_one
      have hprod : 1 ≤ Real.exp 1*(n:ℝ)^8 := one_le_mul_of_one_le_of_one_le he1 hpow
      nlinarith [Real.exp_pos ((n:ℝ)*S z)]
    · have h := Real.exp_le_exp.mpr hnum
      rw [Real.exp_add,Real.exp_add,hlog] at h
      exact h
  have h := mul_le_mul_of_nonneg_right hmax (Real.exp_pos (-(n:ℝ)*S z)).le
  have he : Real.exp ((n:ℝ)*S z)*Real.exp (-(n:ℝ)*S z) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simpa only [mul_assoc,he,mul_one] using h

end
end Yau.Geometry

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

end
end Yau.Probability

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_NormalizedJetBounds
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

lemma real_partial_contDiff (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ fderiv ℝ f x (Pi.single i 1)) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).contDiff.comp
    hdf

lemma real_partial_fderiv_bound (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : _root_.OAI.Yau.Jets.Coord) (i : Fin 4) :
    ‖fderiv ℝ (fun z ↦ fderiv ℝ f z (Pi.single i 1)) x‖ ≤
      ‖iteratedFDeriv ℝ 2 f x‖ := by
  let L : (_root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa [L,Pi.norm_single] using v.le_opNorm (Pi.single i (1:ℝ))
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := (L.hasFDerivAt.comp x
    (hdf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt.hasFDerivAt).fderiv
  change fderiv ℝ (fun z ↦ fderiv ℝ f z (Pi.single i 1)) x = _ at hd
  rw [hd]
  calc
    _ ≤ ‖L‖*‖fderiv ℝ (fderiv ℝ f) x‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*‖fderiv ℝ (fderiv ℝ f) x‖ :=
      mul_le_mul_of_nonneg_right hL (norm_nonneg (fderiv ℝ (fderiv ℝ f) x))
    _ = ‖iteratedFDeriv ℝ 2 f x‖ := by
      rw [one_mul,← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]

lemma scalar_normalization_derivative (q S : _root_.OAI.Yau.Jets.Coord → ℝ) {x : _root_.OAI.Yau.Jets.Coord} {N : ℝ}
    (hq : DifferentiableAt ℝ q x) (hS : DifferentiableAt ℝ S x)
    (hN : 0 ≤ N) :
    ‖fderiv ℝ (fun z ↦ Real.exp (-N*S z)*q z) x‖ ≤
      Real.exp (-N*S x)*(N*‖fderiv ℝ S x‖*|q x|+‖fderiv ℝ q x‖) := by
  have he := ((hS.hasFDerivAt.const_mul (-N)).exp).mul hq.hasFDerivAt
  change HasFDerivAt (fun z ↦ Real.exp (-N*S z)*q z) _ x at he
  rw [he.fderiv]
  have h := norm_add_le
    (Real.exp (-N*S x) • fderiv ℝ q x)
    (q x • (Real.exp (-N*S x) • (-N • fderiv ℝ S x)))
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),abs_neg,
    abs_of_nonneg hN] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma jet_vector_fderiv_bound (q : Fin 5 → _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (hq : ∀ i, DifferentiableAt ℝ (q i) x) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, ‖fderiv ℝ (q i) x‖ ≤ B) :
    ‖fderiv ℝ (fun z ↦ WithLp.toLp 2 (fun i ↦ q i z)) x‖ ≤ 6*B := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 ↦ ℝ)).symm.toContinuousLinearMap
  have hq' : HasFDerivAt (fun z i ↦ q i z)
      (ContinuousLinearMap.pi (fun i ↦ fderiv ℝ (q i) x)) x :=
    hasFDerivAt_pi.mpr (fun i ↦ (hq i).hasFDerivAt)
  have hd := (L.hasFDerivAt.comp x hq').fderiv
  change fderiv ℝ (fun z ↦ WithLp.toLp 2 (fun i ↦ q i z)) x = _ at hd
  rw [hd]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖WithLp.toLp 2 (fun i ↦ fderiv ℝ (q i) x v)‖ ≤ _
  have h := euclidean_toLp_norm_le (fun i ↦ fderiv ℝ (q i) x v)
  have hp : ‖fun i ↦ fderiv ℝ (q i) x v‖ ≤ B*‖v‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact ((fderiv ℝ (q i) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg v))
  norm_num at h
  nlinarith

lemma normalizedRealJet_fderiv_le (f S : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (hS : ContDiff ℝ ∞ S) (x : _root_.OAI.Yau.Jets.Coord) {N : ℝ} (hN : 0 ≤ N) :
    ‖fderiv ℝ (fun z ↦ normalizedRealJet f N (S z) z) x‖ ≤
      6*Real.exp (-N*S x)*(N*‖fderiv ℝ S x‖*
        max |f x| (N⁻¹*‖fderiv ℝ f x‖)+
        max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖)) := by
  let q : Fin 5 → _root_.OAI.Yau.Jets.Coord → ℝ := fun i z ↦
    (Fin.cons (f z) (fun j : Fin 4 ↦ N⁻¹*fderiv ℝ f z (Pi.single j 1)) : Fin 5 → ℝ) i
  have hq (i : Fin 5) : ContDiff ℝ ∞ (q i) := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hf
    · exact contDiff_const.mul (real_partial_contDiff f hf j)
  have hv (i : Fin 5) : |q i x| ≤ max |f x| (N⁻¹*‖fderiv ℝ f x‖) := by
    refine Fin.cases (le_max_left _ _) (fun j ↦ ?_) i
    change |N⁻¹*fderiv ℝ f x (Pi.single j 1)| ≤ _
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hN)]
    apply le_trans ?_ (le_max_right _ _)
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hN)
    simpa [Pi.norm_single] using (fderiv ℝ f x).le_opNorm (Pi.single j (1:ℝ))
  have hd (i : Fin 5) : ‖fderiv ℝ (q i) x‖ ≤
      max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖) := by
    refine Fin.cases (le_max_left _ _) (fun j ↦ ?_) i
    change ‖fderiv ℝ (fun z ↦ N⁻¹*fderiv ℝ f z (Pi.single j 1)) x‖ ≤ _
    rw [((real_partial_contDiff f hf j).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt.hasFDerivAt.const_mul N⁻¹ |>.fderiv]
    change ‖N⁻¹ • fderiv ℝ (fun z ↦ fderiv ℝ f z (Pi.single j 1)) x‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hN)]
    exact (mul_le_mul_of_nonneg_left (real_partial_fderiv_bound f hf x j)
      (inv_nonneg.mpr hN)).trans (le_max_right _ _)
  have heq : (fun z ↦ normalizedRealJet f N (S z) z) =
      fun z ↦ WithLp.toLp 2 (fun i ↦ Real.exp (-N*S z)*q i z) := by
    funext z
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [normalizedRealJet,q,mul_assoc]
  rw [heq]
  have hds := (hS.differentiable (by simp)).differentiableAt (x := x)
  have h := jet_vector_fderiv_bound (fun i z ↦ Real.exp (-N*S z)*q i z) x
    (fun i ↦ ((hds.const_mul (-N)).exp).mul ((hq i).differentiable (by simp)).differentiableAt)
    (B := Real.exp (-N*S x)*(N*‖fderiv ℝ S x‖*max |f x| (N⁻¹*‖fderiv ℝ f x‖)+
      max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖))) (by positivity) (fun i ↦ ?_)
  · simpa [mul_assoc] using h
  · exact (scalar_normalization_derivative (q i) S
      ((hq i).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt hds hN).trans (by gcongr; exact hv i; exact hd i)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_NetProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open Set MeasureTheory
open scoped ENNReal
noncomputable section
variable {Ω X F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F]

lemma finite_small_ball_union (μ : Measure Ω) (t : Finset X) (Z : Ω → X → F)
    (r : ℝ) (p : ℝ≥0∞) (hp : ∀ x ∈ t, μ {ω | ‖Z ω x‖ ≤ r} ≤ p) :
    μ {ω | ∃ x ∈ t, ‖Z ω x‖ ≤ r} ≤ t.card*p := by
  have he : {ω | ∃ x ∈ t, ‖Z ω x‖ ≤ r} = ⋃ x ∈ t, {ω | ‖Z ω x‖ ≤ r} := by
    ext ω
    simp
  rw [he]
  exact (measure_biUnion_finset_le t _).trans (by
    simpa using Finset.sum_le_sum hp)

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℝ F]

lemma neighborhood_net_approximation (t : Finset X) (E : Set X) (Z : X → F)
    {δ R L r : ℝ} (hδ : 0 ≤ δ) (hδR : δ ≤ R) (hL : 0 ≤ L) (hLδ : L*δ ≤ r)
    (hnet : ∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ δ)
    (hdiff : ∀ x ∈ E, ∀ z ∈ Metric.closedBall x R, DifferentiableAt ℝ Z z)
    (hderiv : ∀ x ∈ E, ∀ z ∈ Metric.closedBall x R, ‖fderiv ℝ Z z‖ ≤ L) :
    ∀ x ∈ E, ∃ y ∈ t, ‖Z y-Z x‖ ≤ r := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := hnet x hx
  have hxball : x ∈ Metric.closedBall x R := Metric.mem_closedBall_self (hδ.trans hδR)
  have hyball : y ∈ Metric.closedBall x R := by
    rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev]
    exact hd.trans hδR
  have h := (convex_closedBall x R).norm_image_sub_le_of_norm_fderiv_le
    (hdiff x hx) (hderiv x hx) hxball hyball
  rw [norm_sub_rev y x] at h
  exact ⟨y,hy,h.trans ((mul_le_mul_of_nonneg_left hd hL).trans hLδ)⟩

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_JetNetExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

lemma normalizedRealJet_contDiff (f S : _root_.OAI.Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f)
    (hS : ContDiff ℝ ∞ S) (N : ℝ) :
    ContDiff ℝ ∞ (fun x ↦ normalizedRealJet f N (S x) x) := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 ↦ ℝ)).symm.toContinuousLinearMap
  have hq : ContDiff ℝ ∞ (fun x ↦ (Fin.cons (Real.exp (-N*S x)*f x)
      (fun i : Fin 4 ↦ Real.exp (-N*S x)*N⁻¹*fderiv ℝ f x (Pi.single i 1)) : Fin 5 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact ((contDiff_const.mul hS).exp).mul hf
    · exact (((contDiff_const.mul hS).exp).mul contDiff_const).mul (real_partial_contDiff f hf j)
  exact L.contDiff.comp hq

lemma jet_mesh_arithmetic {N : ℝ} (hN : 1 ≤ N) :
    (4*N^69)⁻¹ ≤ (N^2)⁻¹ ∧ N^13*(4*N^69)⁻¹ ≤ (N^56)⁻¹ := by
  have hp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N^2 ≤ N^69 := pow_le_pow_right₀ hN (by omega)
  constructor
  · apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    nlinarith [pow_pos hp 69]
  · have he : N^13*(4*N^69)⁻¹ = (4*N^56)⁻¹ := by field_simp
    rw [he]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    nlinarith [pow_pos hp 56]

lemma net_failure_le_union {Ω X F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] (μ : Measure Ω) (t : Finset X) (E : Set X)
    (Z : Ω → X → F) (good : Set Ω) (r : ℝ)
    (happrox : ∀ a ∈ good, ∀ x ∈ E, ∃ y ∈ t, ‖Z a y-Z a x‖ ≤ r) :
    μ {a | ∃ x ∈ E, ‖Z a x‖ < r} ≤
      μ goodᶜ+μ {a | ∃ y ∈ t, ‖Z a y‖ ≤ 2*r} := by
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro a ha
  by_cases hg : a ∈ good
  · obtain ⟨x,hx,hr⟩ := ha
    obtain ⟨y,hy,hd⟩ := happrox a hg x hx
    right
    refine ⟨y,hy,?_⟩
    have h := norm_le_norm_sub_add (Z a y) (Z a x)
    linarith
  · exact Or.inl hg

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_NormalizedJetPolynomialBound
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

lemma normalizedRealJet_polynomial_derivative_bound (f S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (hS : ContDiff ℝ ∞ S) (x : _root_.OAI.Yau.Jets.Coord)
    {N A B H : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hs : ‖fderiv ℝ S x‖ ≤ A)
    (hf0 : |f x| ≤ B*N^3*H) (hf1 : ‖fderiv ℝ f x‖ ≤ B*N^4*H)
    (hf2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ B*N^5*H) :
    ‖fderiv ℝ (fun z ↦ normalizedRealJet f N (S z) z) x‖ ≤
      (6*(A+1)*B)*N^4*H*Real.exp (-N*S x) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have h0 : max |f x| (N⁻¹*‖fderiv ℝ f x‖) ≤ B*N^3*H := by
    refine max_le hf0 ?_
    calc
      _ ≤ N⁻¹*(B*N^4*H) := mul_le_mul_of_nonneg_left hf1 (by positivity)
      _ = B*N^3*H := by field_simp
  have h1 : max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖) ≤ B*N^4*H := by
    refine max_le hf1 ?_
    calc
      _ ≤ N⁻¹*(B*N^5*H) := mul_le_mul_of_nonneg_left hf2 (by positivity)
      _ = B*N^4*H := by field_simp
  calc
    _ ≤ 6*Real.exp (-N*S x)*(N*‖fderiv ℝ S x‖*
        max |f x| (N⁻¹*‖fderiv ℝ f x‖)+
        max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖)) :=
      normalizedRealJet_fderiv_le f S hf hS x hNp.le
    _ ≤ 6*Real.exp (-N*S x)*(N*A*(B*N^3*H)+B*N^4*H) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add _ h1
      calc
        _ ≤ N*‖fderiv ℝ S x‖*(B*N^3*H) :=
          mul_le_mul_of_nonneg_left h0 (mul_nonneg hNp.le (norm_nonneg _))
        _ ≤ N*A*(B*N^3*H) :=
          mul_le_mul_of_nonneg_right
            (by simpa only [mul_comm] using mul_le_mul hs (le_refl N) hNp.le hA)
            (mul_nonneg (mul_nonneg hB (pow_nonneg hNp.le _)) hH)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_NeighborhoodJetBound
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

lemma normalized_jet_neighborhood_derivative_bound
    (u S S0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (hS : ContDiff ℝ ∞ S)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} {n : ℕ} (hn : 0 < n) {x z : _root_.OAI.Yau.Jets.Coord}
    (hx : x ∈ highEnvelopeRegion Ω S S0 n) {A B L : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hLn : L ≤ (n:ℝ))
    (hsize : 6*(A+1)*B*Real.exp 1 ≤ (n:ℝ))
    (hz : ‖z-x‖ ≤ ((n:ℝ)^2)⁻¹)
    (hgap : (S0 z-S z)-(S0 x-S x) ≤ L*‖z-x‖)
    (hs : ‖fderiv ℝ S z‖ ≤ A)
    (hb : ∀ k : Fin 3, ‖iteratedFDeriv ℝ k.val u z‖ ≤ B*(n:ℝ)^(k.val+3)*
      max (Real.exp ((n:ℝ)*S z)) (Real.exp ((n:ℝ)*S0 z))) :
    ‖fderiv ℝ (fun y ↦ normalizedRealJet u n (S y) y) z‖ ≤ (n:ℝ)^13 := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  simp only [Fin.val_zero,zero_add,norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h0
  simp only [Fin.val_one,norm_iteratedFDeriv_one] at h1
  have h := normalizedRealJet_polynomial_derivative_bound u S hu hS z hn1 hA hB
    (by positivity) hs h0 h1 h2
  have henv := high_envelope_neighborhood_bound hn hx hL hLn hz hgap
  calc
    _ ≤ (6*(A+1)*B)*(n:ℝ)^4*
        (max (Real.exp ((n:ℝ)*S z)) (Real.exp ((n:ℝ)*S0 z)))*Real.exp (-(n:ℝ)*S z) := h
    _ ≤ (6*(A+1)*B)*(n:ℝ)^4*(Real.exp 1*(n:ℝ)^8) := by
      rw [mul_assoc ((6*(A+1)*B)*(n:ℝ)^4)]
      gcongr
    _ = (6*(A+1)*B*Real.exp 1)*(n:ℝ)^12 := by ring
    _ ≤ (n:ℝ)*(n:ℝ)^12 := mul_le_mul_of_nonneg_right hsize (by positivity)
    _ = (n:ℝ)^13 := by ring

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedJetLowerBound
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Set
open scoped ContDiff
noncomputable section

lemma trig_jet_lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q : E) (t mu B : ℝ) (hmu : 0 < mu) (hB : 0 ≤ B) (hp : ‖p‖ ≤ B) (hq : mu ≤ ‖q‖) :
    mu/(mu+B+1) ≤ |Real.cos t|+‖Real.cos t • p-Real.sin t • q‖ := by
  have he : Real.sin t • q = Real.cos t • p-(Real.cos t • p-Real.sin t • q) := by abel
  have h := norm_sub_le (Real.cos t • p) (Real.cos t • p-Real.sin t • q)
  rw [← he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs] at h
  have h1 : mu*|Real.sin t| ≤ B*|Real.cos t|+‖Real.cos t • p-Real.sin t • q‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hq (abs_nonneg (Real.sin t)),
      mul_le_mul_of_nonneg_left hp (abs_nonneg (Real.cos t))]
  have htrig : 1 ≤ |Real.cos t|+|Real.sin t| := by
    have hc := Real.abs_cos_le_one t
    have hs := Real.abs_sin_le_one t
    have hid := Real.sin_sq_add_cos_sq t
    nlinarith [sq_abs (Real.cos t),sq_abs (Real.sin t),abs_nonneg (Real.cos t),abs_nonneg (Real.sin t)]
  apply (div_le_iff₀ (by positivity : 0 < mu+B+1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left htrig hmu.le,
    mul_nonneg hB (norm_nonneg (Real.cos t • p-Real.sin t • q)),
    mul_nonneg hmu.le (norm_nonneg (Real.cos t • p-Real.sin t • q)),abs_nonneg (Real.cos t)]

lemma oscillatorySeed_normalized_derivative (S T : Coord → ℝ) (N : ℝ) (x : Coord)
    (hS : DifferentiableAt ℝ S x) (hT : DifferentiableAt ℝ T x) (hN : N ≠ 0) :
    N⁻¹ • fderiv ℝ (oscillatorySeed S T N) x =
      Real.exp (N*S x) • (Real.cos (N*T x) • fderiv ℝ S x-Real.sin (N*T x) • fderiv ℝ T x) := by
  have h := ((hS.hasFDerivAt.const_mul N).exp).mul ((hT.hasFDerivAt.const_mul N).cos)
  change HasFDerivAt (oscillatorySeed S T N) _ x at h
  rw [h.fderiv]
  ext v
  simp only [smul_apply,smul_eq_mul,sub_apply,add_apply]
  field_simp
  ring

theorem uniform_oscillatory_seed_jet (S T : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (hT : ContDiff ℝ ∞ T) {Q : Set Coord} (hQ : IsCompact Q)
    (hq : ∀ x ∈ Q, fderiv ℝ T x ≠ 0) :
    ∃ c > 0, ∀ N : ℝ, 0 < N → ∀ x ∈ Q,
      c*Real.exp (N*S x) ≤ |oscillatorySeed S T N x|+N⁻¹*‖fderiv ℝ (oscillatorySeed S T N) x‖ := by
  obtain ⟨mu,hmu,_,_,hql⟩ := compact_positive_bounds hQ (fun x ↦ ‖fderiv ℝ T x‖)
    (hT.continuous_fderiv (by simp)).norm.continuousOn (fun x hx ↦ norm_pos_iff.mpr (hq x hx))
  obtain ⟨B,hB,hpb⟩ := (hQ.image (hS.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨mu/(mu+B+1),by positivity,?_⟩
  intro N hN x hx
  have hb := trig_jet_lower_bound (fderiv ℝ S x) (fderiv ℝ T x) (N*T x) mu B hmu hB.le
    (hpb _ ⟨x,hx,rfl⟩) (hql x hx).1
  have hd := congrArg norm (oscillatorySeed_normalized_derivative S T N x
    (hS.differentiable (by simp)).differentiableAt (hT.differentiable (by simp)).differentiableAt hN.ne')
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hN),abs_of_pos (Real.exp_pos _)] at hd
  rw [hd]
  simpa only [oscillatorySeed,abs_mul,abs_of_pos (Real.exp_pos _),mul_add,mul_comm] using
    mul_le_mul_of_nonneg_left hb (Real.exp_pos (N*S x)).le

end
end Yau.Jets

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
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeFieldBounds
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

theorem lattice_field_derivative_bound (hUD : U ⊆ D) (hUb : Bornology.IsBounded U) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        ContDiff ℝ ∞ (gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) ∧
        ∀ x : _root_.OAI.Yau.Jets.Coord, ∀ k : Fin (k0+1),
          ‖iteratedFDeriv ℝ k.val (gaussianWaveField
            (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) x‖ ≤
          C*(n:ℝ)^(k.val+3)*Real.exp ((n:ℝ)*S x) := by
  obtain ⟨C,hC,hcard⟩ := source_coefficient_card_bound hUb
  have hcw := a.beams.Cw_pos
  have hbc := a.beams.c_pos
  refine ⟨C*a.beams.Cw,mul_pos hC a.beams.Cw_pos,?_⟩
  filter_upwards [a.estimates,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  have := finite_source_grid hUb hnpos
  let hfin := Fintype.ofFinite (SourceGrid U n)
  let := hfin
  refine ⟨hfin,?_⟩
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (hn (latticeFrame a.cover hUD n i.1,i.2)).1
  intro coeff hc
  refine ⟨gaussianWaveField_contDiff V coeff hV,?_⟩
  intro x k
  have hb (i : SourceGrid U n × Fin 3) : ‖iteratedFDeriv ℝ k.val (V i) x‖ ≤
      a.beams.Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S x) := by
    have h := ((hn (latticeFrame a.cover hUD n i.1,i.2)).2.2.2.2 x).1 k
    refine h.trans ?_
    gcongr
    exact sub_le_self _ (by positivity : 0 ≤ a.beams.c*(n:ℝ)*
      (sourceEuclideanNorm (x-coverSourceCenter a.cover (latticeFrame a.cover hUD n i.1)))^2)
  have h := gaussianWaveField_iterated_bound V coeff hV k.val x (by positivity) hc hb
  have hcardR : (Fintype.card (SourceGrid U n × Fin 3):ℝ) ≤ C*(n:ℝ)^2 := by
    simpa only [Nat.card_eq_fintype_card] using hcard n hnpos
  refine h.trans ?_
  calc
    _ ≤ (C*(n:ℝ)^2)*(n:ℝ)*(a.beams.Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S x)) := by
      gcongr
    _ = (C*a.beams.Cw)*(n:ℝ)^(k.val+3)*Real.exp ((n:ℝ)*S x) := by
      rw [pow_add]
      ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_SeededLatticeFieldBounds
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

theorem seeded_lattice_field_derivative_bound (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        let u := fun z ↦ oscillatorySeed S0 T0 n z + gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z
        ContDiff ℝ ∞ u ∧ ∀ x ∈ Q, ∀ k : Fin (k0+1),
          ‖iteratedFDeriv ℝ k.val u x‖ ≤ C*(n:ℝ)^(k.val+3)*
            max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) := by
  have hs (j : Fin (k0+1)) := oscillatorySeed_derivative_bound S0 T0 hS0 hT0 hQ j.val
  choose b hb hseed using hs
  let B : ℝ := ∑ j, b j
  have hB : 0 < B := (hb ⟨0,by omega⟩).trans_le
    (Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _))
  obtain ⟨C,hC,hfield⟩ := a.lattice_field_derivative_bound hUD hUb
  refine ⟨B+C,by positivity,?_⟩
  filter_upwards [hfield,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  obtain ⟨hfin,hbnd⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff hc
  obtain ⟨hV,hVb⟩ := hbnd coeff hc
  have hseedSmooth := oscillatorySeed_contDiff S0 T0 hS0 hT0 (n:ℝ)
  refine ⟨hseedSmooth.add hV,?_⟩
  intro x hx k
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hseed' : ‖iteratedFDeriv ℝ k.val (oscillatorySeed S0 T0 n) x‖ ≤
      B*(n:ℝ)^(k.val+3)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) := by
    have h := hseed k n hn1 x hx
    refine h.trans ?_
    have hbB : b k ≤ B := Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _)
    gcongr
    · omega
    · exact le_max_right _ _
  have hrand : ‖iteratedFDeriv ℝ k.val (gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) x‖ ≤
      C*(n:ℝ)^(k.val+3)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) := by
    refine (hVb x k).trans ?_
    gcongr
    exact le_max_left _ _
  change ‖iteratedFDeriv ℝ k.val (oscillatorySeed S0 T0 n + gaussianWaveField
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hseedSmooth.of_le
    (by exact_mod_cast (show (k.val:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hV.of_le (by exact_mod_cast (show (k.val:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  have h := (norm_add_le _ _).trans (add_le_add hseed' hrand)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeNeighborhoodJets
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

theorem lattice_neighborhood_jet_bound (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    (hS : ContDiff ℝ ∞ S) (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        ∀ x ∈ highEnvelopeRegion Ω S S0 n,
          ∀ z ∈ Metric.closedBall x ((n:ℝ)^2)⁻¹,
            ‖fderiv ℝ (fun y ↦ a.latticeSeededJet hUD n hfin
              (oscillatorySeed S0 T0 n) y coeff) z‖ ≤ (n:ℝ)^13 := by
  obtain ⟨R,hR,hΩR⟩ := hΩ.isBounded.exists_pos_norm_le
  let Q := Metric.closedBall (0:_root_.OAI.Yau.Jets.Coord) (R+1)
  have hQ : IsCompact Q := isCompact_closedBall _ _
  obtain ⟨A,hA,hAb⟩ := (hQ.image (hS.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  have hdS : ContDiff ℝ ∞ (fun z ↦ S0 z-S z) := hS0.sub hS
  obtain ⟨L,hL,hLb⟩ := (hQ.image (hdS.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).isBounded.exists_pos_norm_le
  obtain ⟨B,hB,hfield⟩ := a.seeded_lattice_field_derivative_bound hUD hUb S0 T0 hS0 hT0 hQ
  have hfreq : ∀ᶠ n : ℕ in atTop, max L (6*(A+1)*B*Real.exp 1) ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hfield,hfreq,eventually_gt_atTop (0:ℕ)] with n hn hsize hnpos
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff hc x hx z hz
  obtain ⟨hu,hbnd⟩ := hb coeff hc
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hdist : ‖z-x‖ ≤ ((n:ℝ)^2)⁻¹ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hrad : ((n:ℝ)^2)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ hn1)
  have hxQ : x ∈ Q := by
    change dist x 0 ≤ R+1
    rw [dist_zero_right]
    linarith [hΩR x hx.1]
  have hzQ : z ∈ Q := by
    change dist z 0 ≤ R+1
    rw [dist_zero_right]
    have ht := norm_le_norm_sub_add z x
    linarith [hΩR x hx.1,hdist.trans hrad]
  have hgap : (S0 z-S z)-(S0 x-S x) ≤ L*‖z-x‖ := by
    have h := (convex_closedBall (0:_root_.OAI.Yau.Jets.Coord) (R+1)).norm_image_sub_le_of_norm_fderiv_le
      (fun _ _ ↦ (hdS.differentiable (by simp)).differentiableAt)
      (fun y hy ↦ hLb _ ⟨y,hy,rfl⟩) hxQ hzQ
    exact (le_abs_self _).trans h
  have h := normalized_jet_neighborhood_derivative_bound
    (fun y ↦ oscillatorySeed S0 T0 n y+gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff y)
    S S0 hu hS hnpos hx hA.le hB.le hL.le
    ((le_max_left _ _).trans hsize) ((le_max_right _ _).trans hsize)
    hdist hgap (hAb _ ⟨z,hzQ,rfl⟩)
    (fun k ↦ hbnd z hzQ ⟨k.val,by omega⟩)
  exact h

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_NetDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open Filter
open scoped Topology

lemma net_small_ball_rate (C c n : ℝ) (hc : 0 < c) (hn : 0 < n) :
    C*n^276*(12*(Real.sqrt (c/n))⁻¹*(2/n^56)/Real.sqrt (2*Real.pi))^5 =
      (C*(24/(Real.sqrt c*Real.sqrt (2*Real.pi)))^5)/(n*Real.sqrt n) := by
  have hs := Real.sq_sqrt hn.le
  have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hc0 : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hp0 : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [Real.sqrt_div hc.le,inv_div]
  field_simp
  have hs6 : (Real.sqrt n)^6 = n^3 := by
    calc
      _ = ((Real.sqrt n)^2)^3 := by ring
      _ = n^3 := by rw [hs]
  ring_nf
  rw [hs6]

lemma tendsto_net_rate (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C/((n:ℝ)*Real.sqrt n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt (n:ℝ)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow,Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ hs).inv_tendsto_atTop
  simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using h.const_mul C

lemma tendsto_coefficient_tail_rate (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/8) (by norm_num)).comp hpow
  simpa only [Function.comp_def,Real.rpow_one,mul_zero,mul_assoc,show ∀ x : ℝ, -(1/8)*x = -x/8 by intro x; ring]
    using h.const_mul C

end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SpatialNet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma same_floor_distance {r : ℝ} (hr : 0 < r) {x y : _root_.OAI.Yau.Jets.Coord}
    (h : ∀ i, ⌊x i / r⌋ = ⌊y i / r⌋) : ‖x-y‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg hr.le).mpr
  intro i
  have hx1 := Int.floor_le (x i/r)
  have hx2 := Int.lt_floor_add_one (x i/r)
  have hy1 := Int.floor_le (y i/r)
  have hy2 := Int.lt_floor_add_one (y i/r)
  rw [← h i] at hy1 hy2
  have h1 : x i/r-y i/r ≤ 1 := by linarith
  have h2 : -(1:ℝ) ≤ x i/r-y i/r := by linarith
  rw [← sub_div] at h1 h2
  have h1' := (div_le_iff₀ hr).mp h1
  have h2' := (le_div_iff₀ hr).mp h2
  change |x i-y i| ≤ r
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem bounded_internal_net {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : Bornology.IsBounded Q) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ E : Set _root_.OAI.Yau.Jets.Coord, E ⊆ Q →
      ∃ t : Finset _root_.OAI.Yau.Jets.Coord, (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ E ∧
        (t.card : ℝ) ≤ C*(r⁻¹)^4 ∧
        ∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ r ∧ sourceEuclideanNorm (x-y) ≤ 2*r := by
  classical
  obtain ⟨B,hB,hbound⟩ := hQ.exists_pos_norm_le
  refine ⟨(2*B+5)^4,by positivity,?_⟩
  intro r hr hr1 E hEQ
  let M : ℤ := ⌈B/r⌉+1
  have hM0 : 0 ≤ M := by dsimp [M]; have := Int.ceil_nonneg (div_nonneg hB.le hr.le); omega
  have hceil : B/r ≤ (⌈B/r⌉ : ℝ) := Int.le_ceil _
  have hceil' : (⌈B/r⌉ : ℝ) < B/r+1 := Int.ceil_lt_add_one _
  have hcoords (x : E) (i : Fin 4) : ⌊x.val i/r⌋ ∈ Icc (-M) M := by
    have hi := (norm_le_pi_norm x.val i).trans (hbound x.val (hEQ x.property))
    change |x.val i| ≤ B at hi
    have hxi := abs_le.mp hi
    have hx1 := Int.floor_le (x.val i/r)
    have hx2 := Int.lt_floor_add_one (x.val i/r)
    have hu : x.val i/r ≤ B/r := div_le_div_of_nonneg_right hxi.2 hr.le
    have hl : -B/r ≤ x.val i/r := div_le_div_of_nonneg_right hxi.1 hr.le
    rw [neg_div] at hl
    have hMc : (M:ℝ) = (⌈B/r⌉:ℝ)+1 := by simp [M]
    constructor
    · have : -(M:ℝ) ≤ (⌊x.val i/r⌋:ℝ) := by linarith
      exact_mod_cast this
    · have : (⌊x.val i/r⌋:ℝ) ≤ (M:ℝ) := by linarith
      exact_mod_cast this
  let Box := Fin 4 → Icc (-M) M
  let f : E → Box := fun x i ↦ ⟨⌊x.val i/r⌋,hcoords x i⟩
  let R := Set.range f
  let rep : R → E := fun z ↦ Classical.choose z.property
  have hrep (z : R) : f (rep z) = z.val := Classical.choose_spec z.property
  let t : Finset _root_.OAI.Yau.Jets.Coord := Finset.univ.image (fun z : R ↦ (rep z).val)
  refine ⟨t,?_,?_,?_⟩
  · intro y hy
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hy
    exact (rep z).property
  · have hc : t.card ≤ Fintype.card Box :=
      (Finset.card_image_le).trans (by
        simpa using Fintype.card_le_of_injective (fun z : R ↦ z.val) Subtype.val_injective)
    have hbox : Fintype.card Box = ((2*M+1).toNat)^4 := by
      simp [Box,Int.card_Icc,show M+1- -M = 2*M+1 by ring]
    rw [hbox] at hc
    have hcR : (t.card:ℝ) ≤ ((2*M+1).toNat:ℝ)^4 := by exact_mod_cast hc
    have hcast : ((2*M+1).toNat:ℝ) = 2*(M:ℝ)+1 := by
      have hi : ((2*M+1).toNat:ℤ) = 2*M+1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hi
    rw [hcast] at hcR
    have hri : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
    have hMc : (M:ℝ) < B/r+2 := by dsimp [M]; push_cast <;> linarith
    have hm : 2*(M:ℝ)+1 ≤ (2*B+5)*r⁻¹ := by
      rw [div_eq_mul_inv] at hMc
      nlinarith
    calc
      (t.card:ℝ) ≤ (2*(M:ℝ)+1)^4 := hcR
      _ ≤ ((2*B+5)*r⁻¹)^4 := pow_le_pow_left₀ (by positivity) hm 4
      _ = (2*B+5)^4*(r⁻¹)^4 := mul_pow _ _ _
  · intro x hx
    let z : R := ⟨f ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩⟩
    refine ⟨(rep z).val,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩,?_⟩
    have he : ∀ i, ⌊x i/r⌋ = ⌊(rep z).val i/r⌋ := by
      intro i
      exact (congrArg Subtype.val (congrFun (hrep z) i)).symm
    have hd := same_floor_distance hr he
    exact ⟨hd,(sourceEuclideanNorm_le _).trans (by linarith)⟩

theorem jet_scale_internal_net {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : Bornology.IsBounded Q) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ E : Set _root_.OAI.Yau.Jets.Coord, E ⊆ Q →
      ∃ t : Finset _root_.OAI.Yau.Jets.Coord, (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ E ∧
        (t.card : ℝ) ≤ C*(n:ℝ)^276 ∧
        ∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ (4*(n:ℝ)^69)⁻¹ ∧
          sourceEuclideanNorm (x-y) ≤ (2*(n:ℝ)^69)⁻¹ := by
  obtain ⟨C,hC,hnet⟩ := bounded_internal_net hQ
  refine ⟨C*4^4,by positivity,?_⟩
  intro n hn E hEQ
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by positivity
  have hpow : (1:ℝ) ≤ (n:ℝ)^69 := one_le_pow₀ hnR
  obtain ⟨t,ht,hcard,hcover⟩ := hnet (4*(n:ℝ)^69)⁻¹ (by positivity)
    ((inv_le_one₀ (by positivity)).mpr (by linarith)) E hEQ
  refine ⟨t,ht,?_,?_⟩
  · convert hcard using 1
    all_goals try with_reducible_and_instances rfl
    simp only [inv_inv,mul_pow,← pow_mul]
    ring
  · intro x hx
    obtain ⟨y,hy,hd,he⟩ := hcover x hx
    refine ⟨y,hy,hd,?_⟩
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeNetSmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

lemma measurable_latticeSeededJet (hUD : U ⊆ D) (n : ℕ)
    (hfin : Fintype (SourceGrid U n)) (seed : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (hs : DifferentiableAt ℝ seed x)
    (hV : ∀ z j, DifferentiableAt ℝ (latticeWave a.cover a.beams hUD n z j) x) :
    Measurable (a.latticeSeededJet hUD n hfin seed x) := by
  let := hfin
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have he : a.latticeSeededJet hUD n hfin seed x = fun coeff ↦
      normalizedRealJet seed n (S x) x +
        pairJetMap (jetWaveCoefficients V n (S x) x) (WithLp.toLp 2 coeff) := by
    funext coeff
    exact seeded_gaussian_jet_eq V seed n (S x) x (fun i ↦ hV i.1 i.2) hs coeff
  rw [he]
  fun_prop

theorem actual_lattice_net_small_ball (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ E : Set _root_.OAI.Yau.Jets.Coord, E ⊆ Q → ∃ t : Finset _root_.OAI.Yau.Jets.Coord,
        (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ E ∧ (t.card : ℝ) ≤ C*(n:ℝ)^276 ∧
        (∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ (4*(n:ℝ)^69)⁻¹ ∧
          sourceEuclideanNorm (x-y) ≤ (2*(n:ℝ)^69)⁻¹) ∧
        ∀ seed : _root_.OAI.Yau.Jets.Coord → ℝ, (∀ x ∈ Q, DifferentiableAt ℝ seed x) →
          gaussianPairs {coeff | ∃ x ∈ t,
            ‖a.latticeSeededJet hUD n hfin seed x coeff‖ ≤ 2/(n:ℝ)^56} ≤
          ENNReal.ofReal (C*(n:ℝ)^276*
            (12*(Real.sqrt (c/(n:ℝ)))⁻¹*(2/(n:ℝ)^56)/Real.sqrt (2*Real.pi))^5) := by
  obtain ⟨c,hc,hsmall⟩ := a.actual_lattice_gaussian_small_ball hUD hU hUb hQ hQU
  obtain ⟨C,hC,hnet⟩ := jet_scale_internal_net hQ.isBounded
  refine ⟨c,hc,C,hC,?_⟩
  filter_upwards [hsmall,lattice_wave_estimates a.cover a.beams hUD,
    eventually_gt_atTop (0:ℕ)] with n hn hw hnpos
  obtain ⟨hfin,hp⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro E hEQ
  obtain ⟨t,ht,hcard,hcover⟩ := hnet n hnpos E hEQ
  refine ⟨t,ht,hcard,hcover,?_⟩
  intro seed hs
  let b := (12*(Real.sqrt (c/(n:ℝ)))⁻¹*(2/(n:ℝ)^56)/Real.sqrt (2*Real.pi))^5
  have hb : 0 ≤ b := by dsimp [b] <;> positivity
  have hp' (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∈ t) :
      gaussianPairs {coeff | ‖a.latticeSeededJet hUD n hfin seed x coeff‖ ≤ 2/(n:ℝ)^56} ≤
        ENNReal.ofReal b := by
    have hxQ := hEQ (ht hx)
    have h := hp seed x hxQ (hs x hxQ) (2/(n:ℝ)^56) (by positivity)
    rw [Measure.map_apply (a.measurable_latticeSeededJet hUD n hfin seed x (hs x hxQ)
      (fun z j ↦ ((hw z j).1.differentiable (by simp)).differentiableAt))
      (measurableSet_le (by fun_prop) measurable_const)] at h
    exact h
  have hu := finite_small_ball_union gaussianPairs t
    (fun coeff x ↦ a.latticeSeededJet hUD n hfin seed x coeff)
    (2/(n:ℝ)^56) (ENNReal.ofReal b) hp'
  refine hu.trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  gcongr
  exact_mod_cast (ENNReal.ofReal_le_ofReal hcard)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeProbabilityRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
noncomputable section

lemma lattice_coefficient_event_failure {U : Set _root_.OAI.Yau.Jets.Coord} (hU : Bornology.IsBounded U) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ hfin : Fintype (SourceGrid U n),
      letI := hfin
      (gaussianPairs (ι := SourceGrid U n × Fin 3)) (coefficientEvent (n:ℝ))ᶜ ≤
        ENNReal.ofReal (C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) := by
  obtain ⟨C,hC,hcard⟩ := source_coefficient_card_bound hU
  refine ⟨4*C,by positivity,?_⟩
  intro n hn hfin
  let := hfin
  have h := coefficient_event_failure (ι := SourceGrid U n × Fin 3)
    (r := (n:ℝ)) (by positivity)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc : (Fintype.card (SourceGrid U n × Fin 3):ℝ) ≤ C*(n:ℝ)^2 := by
    simpa only [Nat.card_eq_fintype_card] using hcard n hn
  nlinarith [mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (-(n:ℝ)^2/8))]

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem actual_lattice_net_failure_rate (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ B > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ E : Set _root_.OAI.Yau.Jets.Coord, E ⊆ Q → ∃ t : Finset _root_.OAI.Yau.Jets.Coord,
        (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ E ∧
        (∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ (4*(n:ℝ)^69)⁻¹ ∧
          sourceEuclideanNorm (x-y) ≤ (2*(n:ℝ)^69)⁻¹) ∧
        ∀ seed : _root_.OAI.Yau.Jets.Coord → ℝ, (∀ x ∈ Q, DifferentiableAt ℝ seed x) →
          gaussianPairs {coeff | ∃ x ∈ t,
            ‖a.latticeSeededJet hUD n hfin seed x coeff‖ ≤ 2/(n:ℝ)^56} ≤
          ENNReal.ofReal (B/((n:ℝ)*Real.sqrt n)) := by
  obtain ⟨c,hc,C,hC,hnet⟩ := a.actual_lattice_net_small_ball hUD hU hUb hQ hQU
  refine ⟨C*(24/(Real.sqrt c*Real.sqrt (2*Real.pi)))^5,by positivity,?_⟩
  filter_upwards [hnet,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro E hEQ
  obtain ⟨t,ht,_,hcover,hprob⟩ := hb E hEQ
  refine ⟨t,ht,hcover,?_⟩
  intro seed hs
  have h := hprob seed hs
  rw [net_small_ball_rate C c n hc (by positivity)] at h
  exact h

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_HighRegionNonvanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem high_region_nonvanishing_probability (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∃ B > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      gaussianPairs {coeff | ∃ x ∈ highEnvelopeRegion Ω S S0 n,
        ‖a.latticeSeededJet hUD n hfin (oscillatorySeed S0 T0 n) x coeff‖ < ((n:ℝ)^56)⁻¹} ≤
      ENNReal.ofReal (B/((n:ℝ)*Real.sqrt n)+C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) := by
  obtain ⟨Q,hQ,hQU,_,hEQ⟩ := high_envelope_fixed_compact hΩ hU S S0
    hS.continuous hS0.continuous hd hgap
  obtain ⟨B,hB,hnet⟩ := a.actual_lattice_net_failure_rate hUD hU hUb hQ hQU
  obtain ⟨C,hC,hcoeff⟩ := lattice_coefficient_event_failure hUb
  have hder := a.lattice_neighborhood_jet_bound hUD hUb hS S0 T0 hS0 hT0 hΩ hk0
  refine ⟨B,hB,C,hC,?_⟩
  filter_upwards [hnet,hder,hEQ,lattice_wave_estimates a.cover a.beams hUD,
    eventually_gt_atTop (0:ℕ)] with n hn hdn hEn hw hnpos
  obtain ⟨hfin,hnb⟩ := hn
  obtain ⟨hfin',hdb⟩ := hdn
  cases Subsingleton.elim hfin' hfin
  let := hfin
  refine ⟨hfin,?_⟩
  obtain ⟨t,ht,hcover,hprob⟩ := hnb (highEnvelopeRegion Ω S S0 n) hEn
  let Z := fun coeff x ↦ a.latticeSeededJet hUD n hfin (oscillatorySeed S0 T0 n) x coeff
  have hs := oscillatorySeed_contDiff S0 T0 hS0 hT0 (n:ℝ)
  have hZ (coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ) : ContDiff ℝ ∞ (Z coeff) := by
    apply normalizedRealJet_contDiff _ S _ hS n
    exact hs.add (gaussianWaveField_contDiff _ coeff
      (fun i ↦ (hw i.1 i.2).1))
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have harith := jet_mesh_arithmetic hn1
  have happrox : ∀ coeff ∈ coefficientEvent (n:ℝ),
      ∀ x ∈ highEnvelopeRegion Ω S S0 n, ∃ y ∈ t,
        ‖Z coeff y-Z coeff x‖ ≤ ((n:ℝ)^56)⁻¹ := by
    intro coeff hc
    apply neighborhood_net_approximation t (highEnvelopeRegion Ω S S0 n) (Z coeff)
      (δ := (4*(n:ℝ)^69)⁻¹) (R := ((n:ℝ)^2)⁻¹) (L := (n:ℝ)^13)
      (by positivity) harith.1 (by positivity) harith.2
    · intro x hx
      obtain ⟨y,hy,hxy,_⟩ := hcover x hx
      exact ⟨y,hy,hxy⟩
    · exact fun _ _ _ _ ↦ ((hZ coeff).differentiable (by simp)).differentiableAt
    · exact hdb coeff hc
  have h := net_failure_le_union gaussianPairs t (highEnvelopeRegion Ω S S0 n)
    Z (coefficientEvent (n:ℝ)) (((n:ℝ)^56)⁻¹) happrox
  have hp := hprob (oscillatorySeed S0 T0 n)
    (fun _ _ ↦ (hs.differentiable (by simp)).differentiableAt)
  have hpc : gaussianPairs {coeff | ∃ y ∈ t, ‖Z coeff y‖ ≤ 2*((n:ℝ)^56)⁻¹} ≤
      ENNReal.ofReal (B/((n:ℝ)*Real.sqrt n)) := by
    simpa only [div_eq_mul_inv] using hp
  refine h.trans ((add_le_add (hcoeff n hnpos hfin) hpc).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FirstJetSize
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability
noncomputable section

lemma firstJetSize_nonneg (f : _root_.OAI.Yau.Jets.Coord → ℝ) {N : ℝ} (hN : 0 ≤ N) (x : _root_.OAI.Yau.Jets.Coord) :
    0 ≤ firstJetSize f N x := by unfold firstJetSize; positivity

lemma normalizedRealJet_norm_le (f : _root_.OAI.Yau.Jets.Coord → ℝ) (S : ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    {N : ℝ} (hN : 0 ≤ N) :
    ‖normalizedRealJet f N S x‖ ≤ 6*Real.exp (-N*S)*firstJetSize f N x := by
  let v : Fin 5 → ℝ := Fin.cons (Real.exp (-N*S)*f x)
    (fun i : Fin 4 ↦ Real.exp (-N*S)*N⁻¹*fderiv ℝ f x (Pi.single i 1))
  have hb : ‖v‖ ≤ Real.exp (-N*S)*firstJetSize f N x := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (firstJetSize_nonneg f hN x))).mpr
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change |Real.exp (-N*S)*f x| ≤ _
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact le_add_of_nonneg_right (by positivity)
    · change |Real.exp (-N*S)*N⁻¹*fderiv ℝ f x (Pi.single j 1)| ≤ _
      rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (inv_nonneg.mpr hN),mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hj : |fderiv ℝ f x (Pi.single j 1)| ≤ ‖fderiv ℝ f x‖ := by
        simpa [Pi.norm_single] using (fderiv ℝ f x).le_opNorm (Pi.single j (1:ℝ))
      exact (mul_le_mul_of_nonneg_left hj (inv_nonneg.mpr hN)).trans
        (le_add_of_nonneg_left (abs_nonneg _))
  have h := euclidean_toLp_norm_le v
  norm_num at h
  exact h.trans (by change 6*‖v‖ ≤ _; nlinarith)

lemma firstJetSize_sub_le (f g : _root_.OAI.Yau.Jets.Coord → ℝ) {N : ℝ} (hN : 0 ≤ N) (x : _root_.OAI.Yau.Jets.Coord)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    firstJetSize (fun z ↦ f z-g z) N x ≤ firstJetSize f N x+firstJetSize g N x := by
  unfold firstJetSize
  rw [fderiv_fun_sub hf hg]
  have h := mul_le_mul_of_nonneg_left (norm_sub_le (fderiv ℝ f x) (fderiv ℝ g x))
    (inv_nonneg.mpr hN)
  nlinarith [abs_sub (f x) (g x)]

lemma firstJetSize_seed_dominance (seed W : _root_.OAI.Yau.Jets.Coord → ℝ) {N : ℝ} (hN : 0 ≤ N)
    (x : _root_.OAI.Yau.Jets.Coord) (hs : DifferentiableAt ℝ seed x) (hW : DifferentiableAt ℝ W x)
    {c E : ℝ} (hseed : c*E ≤ firstJetSize seed N x)
    (hrandom : firstJetSize W N x ≤ (c/2)*E) :
    (c/2)*E ≤ firstJetSize (fun z ↦ seed z+W z) N x := by
  have h := firstJetSize_sub_le (fun z ↦ seed z+W z) W hN x (hs.fun_add hW) hW
  have he : (fun z ↦ (seed z+W z)-W z) = seed := by funext z; ring
  rw [he] at h
  linarith

lemma high_region_firstJetSize_lower {Ω : Set _root_.OAI.Yau.Jets.Coord} {S S0 : _root_.OAI.Yau.Jets.Coord → ℝ}
    {n : ℕ} (hn : 24 ≤ n) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ highEnvelopeRegion Ω S S0 n)
    (f : _root_.OAI.Yau.Jets.Coord → ℝ) (hjet : ((n:ℝ)^56)⁻¹ ≤ ‖normalizedRealJet f n (S x) x‖) :
    (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) ≤
      firstJetSize f n x := by
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn6 : (24:ℝ) ≤ n := by exact_mod_cast hn
  have h := hjet.trans (normalizedRealJet_norm_le f (S x) x hnR.le)
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos ((n:ℝ)*S x)).le
  have he : Real.exp (-(n:ℝ)*S x)*Real.exp ((n:ℝ)*S x) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hh : ((n:ℝ)^56)⁻¹*Real.exp ((n:ℝ)*S x) ≤ 6*firstJetSize f n x := by
    have hex : 6*Real.exp (-(n:ℝ)*S x)*firstJetSize f n x*Real.exp ((n:ℝ)*S x) =
        6*firstJetSize f n x := by
      calc
        _ = 6*(Real.exp (-(n:ℝ)*S x)*Real.exp ((n:ℝ)*S x))*firstJetSize f n x := by ring
        _ = _ := by rw [he]; ring
    rwa [hex] at hmul
  have henv := high_envelope_bound hnpos hx
  calc
    _ ≤ (4*((n:ℝ)^65)⁻¹)*((n:ℝ)^8*Real.exp ((n:ℝ)*S x)) :=
      mul_le_mul_of_nonneg_left henv (by positivity)
    _ = (4*((n:ℝ)^57)⁻¹)*Real.exp ((n:ℝ)*S x) := by field_simp
    _ ≤ firstJetSize f n x := by
      have he' : ((n:ℝ)^56)⁻¹ = (n:ℝ)*((n:ℝ)^57)⁻¹ := by field_simp
      rw [he'] at hh
      have hp := firstJetSize_nonneg f hnR.le x
      nlinarith [mul_nonneg (sub_nonneg.mpr hn6)
        (mul_nonneg (inv_nonneg.mpr (pow_nonneg hnR.le 57)) (Real.exp_pos ((n:ℝ)*S x)).le)]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LowRegionSeedDominance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section

lemma low_envelope_ratio {Ω : Set _root_.OAI.Yau.Jets.Coord} {S S0 : _root_.OAI.Yau.Jets.Coord → ℝ} {n : ℕ}
    (hn : 0 < n) {x : _root_.OAI.Yau.Jets.Coord} (hx : x ∈ Ω) (hxE : x ∉ highEnvelopeRegion Ω S S0 n) :
    Real.exp ((n:ℝ)*S x) ≤ ((n:ℝ)^8)⁻¹*Real.exp ((n:ℝ)*S0 x) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hgap : S x-S0 x < -8*Real.log (n:ℝ)/(n:ℝ) := by
    by_contra hh
    exact hxE ⟨hx,le_of_not_gt hh⟩
  have hb := (lt_div_iff₀ hnR).mp hgap
  have he : (n:ℝ)*S x ≤ (n:ℝ)*S0 x-8*Real.log (n:ℝ) := by nlinarith
  have hlog : Real.exp (8*Real.log (n:ℝ)) = (n:ℝ)^8 := by
    rw [show (8:ℝ)*Real.log (n:ℝ) = (8:ℕ)*Real.log (n:ℝ) by norm_num,
      Real.exp_nat_mul,Real.exp_log hnR]
  have h := Real.exp_le_exp.mpr he
  rw [Real.exp_sub,hlog] at h
  simpa [div_eq_mul_inv,mul_comm] using h

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem low_region_seed_dominance (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsCompact Ω) (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0) (hk0 : 1 ≤ k0) :
    ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) → ∀ x ∈ Ω, x ∉ highEnvelopeRegion Ω S S0 n →
        (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) ≤
          firstJetSize (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
            (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z) n x := by
  obtain ⟨c,hc,hseed⟩ := uniform_oscillatory_seed_jet S0 T0 hS0 hT0 hΩ hq
  obtain ⟨C,hC,hfield⟩ := a.lattice_field_derivative_bound hUD hUb
  have hfreq : ∀ᶠ n : ℕ in atTop, max 1 (max (4*C/c) (8/c)) ≤ (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hfield,hfreq,eventually_gt_atTop (0:ℕ)] with n hn hf hnpos
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,?_⟩
  intro coeff hcoeff x hx hxE
  obtain ⟨hW,hWb⟩ := hb coeff hcoeff
  let W := gaussianWaveField
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn1 : (1:ℝ) ≤ n := (le_max_left _ _).trans hf
  have hnC : 4*C/c ≤ (n:ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hf)
  have hnc : 8/c ≤ (n:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hf)
  have hratio := low_envelope_ratio hnpos hx hxE
  have hrand : firstJetSize W n x ≤ 2*C*((n:ℝ)^5)⁻¹*Real.exp ((n:ℝ)*S0 x) := by
    have h0 := hWb x ⟨0,by omega⟩
    have h1 := hWb x ⟨1,by omega⟩
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h0
    simp only [norm_iteratedFDeriv_one] at h1
    have hval : firstJetSize W n x ≤ 2*C*(n:ℝ)^3*Real.exp ((n:ℝ)*S x) := by
      have hi := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hnR.le)
      have he : (n:ℝ)⁻¹*(C*(n:ℝ)^4*Real.exp ((n:ℝ)*S x)) =
          C*(n:ℝ)^3*Real.exp ((n:ℝ)*S x) := by field_simp
      change (n:ℝ)⁻¹*‖fderiv ℝ W x‖ ≤ _ at hi
      rw [he] at hi
      change |W x| ≤ C*(n:ℝ)^3*Real.exp ((n:ℝ)*S x) at h0
      unfold firstJetSize
      linarith
    refine hval.trans ?_
    calc
      _ ≤ 2*C*(n:ℝ)^3*(((n:ℝ)^8)⁻¹*Real.exp ((n:ℝ)*S0 x)) := by gcongr
      _ = _ := by field_simp
  have hsmall : 2*C*((n:ℝ)^5)⁻¹ ≤ c/2 := by
    have h5 : (n:ℝ) ≤ (n:ℝ)^5 := by simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 5 by omega)
    have hC' := (div_le_iff₀ hc).mp hnC
    change 2*C/(n:ℝ)^5 ≤ c/2
    apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)^5)).mpr
    change 2*C ≤ c/2*(n:ℝ)^5
    nlinarith
  have hlower := firstJetSize_seed_dominance (oscillatorySeed S0 T0 n) W hnR.le x
    ((oscillatorySeed_contDiff S0 T0 hS0 hT0 n).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
    (hW.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (hseed n hnR x hx)
    (hrand.trans (mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le))
  have hmax : max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)) = Real.exp ((n:ℝ)*S0 x) := by
    apply max_eq_right
    have hi : ((n:ℝ)^8)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ hn1)
    exact hratio.trans (by nlinarith [Real.exp_pos ((n:ℝ)*S0 x)])
  rw [hmax]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) hlower
  have h65 : (n:ℝ) ≤ (n:ℝ)^65 := by simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 65 by omega)
  have hc' := (div_le_iff₀ hc).mp hnc
  change 4/(n:ℝ)^65 ≤ c/2
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)^65)).mpr
  nlinarith

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalFirstJetNonvanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem local_first_jet_nonvanishing (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∃ B > 0, ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      gaussianPairs {coeff | ∃ x ∈ Ω,
        firstJetSize (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z) n x <
        (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x))} ≤
      ENNReal.ofReal (B/((n:ℝ)*Real.sqrt n)+C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) := by
  obtain ⟨B,hB,C,hC,hhigh⟩ := a.high_region_nonvanishing_probability
    hUD hU hUb hS S0 T0 hS0 hT0 hΩ hk0 hd hgap
  obtain ⟨D,hD,htail⟩ := lattice_coefficient_event_failure hUb
  have hlow := a.low_region_seed_dominance hUD hUb S0 T0 hS0 hT0 hΩ hq (by omega)
  refine ⟨B,hB,C+D,by positivity,?_⟩
  filter_upwards [hhigh,hlow,eventually_ge_atTop (24:ℕ)] with n hn hln hn6
  obtain ⟨hfin,hprob⟩ := hn
  obtain ⟨hfin',hdom⟩ := hln
  cases Subsingleton.elim hfin' hfin
  let := hfin
  refine ⟨hfin,?_⟩
  let u := fun coeff z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z
  have hsub : {coeff | ∃ x ∈ Ω, firstJetSize (u coeff) n x <
      (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x))} ⊆
      (coefficientEvent (n:ℝ))ᶜ ∪ {coeff | ∃ x ∈ highEnvelopeRegion Ω S S0 n,
        ‖a.latticeSeededJet hUD n hfin (oscillatorySeed S0 T0 n) x coeff‖ < ((n:ℝ)^56)⁻¹} := by
    intro coeff hc
    by_cases hevent : coeff ∈ coefficientEvent (n:ℝ)
    · obtain ⟨x,hx,hbad⟩ := hc
      by_cases hxE : x ∈ highEnvelopeRegion Ω S S0 n
      · right
        refine ⟨x,hxE,?_⟩
        by_contra hjet
        have hj : ((n:ℝ)^56)⁻¹ ≤ ‖normalizedRealJet (u coeff) n (S x) x‖ := le_of_not_gt hjet
        exact (not_lt_of_ge (high_region_firstJetSize_lower hn6 hxE (u coeff) hj)) hbad
      · exact False.elim ((not_lt_of_ge (hdom coeff hevent x hx hxE)) hbad)
    · exact Or.inl hevent
  have h := (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (htail n (by omega) hfin) hprob))
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem local_first_jet_failure_tends_zero (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      gaussianPairs {coeff | ∃ x ∈ Ω,
        firstJetSize (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z) n x <
        (4*((n:ℝ)^65)⁻¹)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x))} ≤
      ENNReal.ofReal ε := by
  obtain ⟨B,_,C,_,hprob⟩ := a.local_first_jet_nonvanishing hUD hU hUb hS
    S0 T0 hS0 hT0 hΩ hk0 hq hd hgap
  have hrate : Tendsto (fun n : ℕ ↦ B/((n:ℝ)*Real.sqrt n)+
      C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) atTop (𝓝 0) := by
    simpa only [add_zero] using (tendsto_net_rate B).add (tendsto_coefficient_tail_rate C)
  intro ε hε
  filter_upwards [hprob,hrate.eventually (gt_mem_nhds hε)] with n hn hsmall
  obtain ⟨hfin,hp⟩ := hn
  exact ⟨hfin,hp.trans (ENNReal.ofReal_le_ofReal hsmall.le)⟩

end LocalCompactWaveData
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

lemma firstJetSize_le_source (f : _root_.OAI.Yau.Jets.Coord → ℝ) {N : ℝ} (hN : 0 ≤ N) (x : _root_.OAI.Yau.Jets.Coord) :
    firstJetSize f N x ≤ 4*sourceFirstJetSize f N x := by
  have h := mul_le_mul_of_nonneg_left (covector_norm_le_source (fderiv ℝ f x)) (inv_nonneg.mpr hN)
  unfold firstJetSize sourceFirstJetSize
  nlinarith [abs_nonneg (f x)]

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem source_first_jet_failure_tends_zero (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      gaussianPairs {coeff | ∃ x ∈ Ω,
        sourceFirstJetSize (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z) n x <
        ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x))} ≤
      ENNReal.ofReal ε := by
  intro ε hε
  filter_upwards [a.local_first_jet_failure_tends_zero hUD hU hUb hS
    S0 T0 hS0 hT0 hΩ hk0 hq hd hgap ε hε,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  obtain ⟨hfin,hb⟩ := hn
  let := hfin
  refine ⟨hfin,(measure_mono ?_).trans hb⟩
  intro coeff hbad
  obtain ⟨x,hx,hsmall⟩ := hbad
  refine ⟨x,hx,?_⟩
  have h := firstJetSize_le_source
    (fun z ↦ oscillatorySeed S0 T0 n z+gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z)
    (N := (n:ℝ)) (by positivity) x
  nlinarith

end LocalCompactWaveData
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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FirstJetGoodEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Yau.Probability Set MeasureTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma seeded_firstJetSize_continuous (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed) (N : ℝ) (x : _root_.OAI.Yau.Jets.Coord) :
    Continuous (fun a : ι × Fin 2 → ℝ ↦
      sourceFirstJetSize (fun y ↦ seed y+gaussianWaveField V a y) N x) := by
  have hc (ds : List (Fin 4)) :=
    (seeded_partial_joint_continuous V seed hV hs ds).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ι × Fin 2 → ℝ ↦ x)))
  have hd (i : Fin 4) : Continuous (fun a : ι × Fin 2 → ℝ ↦
      fderiv ℝ (fun y ↦ seed y+gaussianWaveField V a y) x (Pi.single i 1)) := by
    simpa only [Function.comp_def,partialJet,id_eq] using hc [i]
  unfold sourceFirstJetSize sourceEuclideanNorm
  apply (show Continuous (fun a : ι × Fin 2 → ℝ ↦ seed x+gaussianWaveField V a x) from
    by simpa only [Function.comp_def,partialJet,id_eq] using hc []).abs.add
  exact continuous_const.mul (continuous_finsetSum _ (fun i _ ↦ (hd i).pow 2)).sqrt

lemma firstJetGoodEvent_isClosed (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (N : ℝ) (Ω : Set _root_.OAI.Yau.Jets.Coord) (b : _root_.OAI.Yau.Jets.Coord → ℝ) : IsClosed (firstJetGoodEvent V seed N Ω b) := by
  simp only [firstJetGoodEvent,ofPred_forall]
  exact isClosed_iInter (fun x ↦ isClosed_iInter (fun _ ↦
    isClosed_le continuous_const (seeded_firstJetSize_continuous V seed hV hs N x)))

omit [Fintype ι] in
lemma coefficientEvent_isClosed (r : ℝ) : IsClosed (coefficientEvent (ι := ι) r) := by
  simp only [coefficientEvent,ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_le _ continuous_const
  fun_prop

lemma coefficientJetGoodEvent_measurable (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hs : ContDiff ℝ ∞ seed)
    (N : ℝ) (Ω : Set _root_.OAI.Yau.Jets.Coord) (b : _root_.OAI.Yau.Jets.Coord → ℝ) :
    MeasurableSet (coefficientJetGoodEvent V seed N Ω b) :=
  ((coefficientEvent_isClosed N).inter (firstJetGoodEvent_isClosed V seed hV hs N Ω b)).measurableSet

lemma coefficientJetGoodEvent_failure_le (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N : ℝ) (Ω : Set _root_.OAI.Yau.Jets.Coord) (b : _root_.OAI.Yau.Jets.Coord → ℝ) :
    gaussianPairs (coefficientJetGoodEvent V seed N Ω b)ᶜ ≤
      gaussianPairs (coefficientEvent (ι := ι) N)ᶜ +
      gaussianPairs {a | ∃ x ∈ Ω, sourceFirstJetSize
        (fun y ↦ seed y+gaussianWaveField V a y) N x < b x} := by
  have he : (firstJetGoodEvent V seed N Ω b)ᶜ =
      {a | ∃ x ∈ Ω, sourceFirstJetSize (fun y ↦ seed y+gaussianWaveField V a y) N x < b x} := by
    ext a
    simp [firstJetGoodEvent,not_forall,not_le]
  rw [coefficientJetGoodEvent,compl_inter,he]
  exact measure_union_le _ _

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeGoodEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
  {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_good_event_probability_oai (hUD : U ⊆ D) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hS : ContDiff ℝ ∞ S)
    (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    {Ω : Set _root_.OAI.Yau.Jets.Coord} (hΩ : IsCompact Ω) (hk0 : 2 ≤ k0)
    (hq : ∀ x ∈ Ω, fderiv ℝ T0 x ≠ 0)
    {d : ℝ} (hd : 0 < d) (hgap : ∀ x ∈ Ω, x ∉ U → S x-S0 x ≤ -d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      MeasurableSet (a.latticeGoodEvent hUD n hfin S0 T0 Ω) ∧
      gaussianPairs (a.latticeGoodEvent hUD n hfin S0 T0 Ω)ᶜ ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨C,hC,hcoeff⟩ := lattice_coefficient_event_failure hUb
  have htail := (tendsto_coefficient_tail_rate C).eventually (gt_mem_nhds (by linarith : 0 < ε/2))
  filter_upwards [a.source_first_jet_failure_tends_zero hUD hU hUb hS S0 T0 hS0 hT0
    hΩ hk0 hq hd hgap (ε/2) (by linarith),htail,a.estimates,eventually_gt_atTop (0:ℕ)] with n hn ht he hn0
  obtain ⟨hfin,hjet⟩ := hn
  let := hfin
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  have hV (i : SourceGrid U n × Fin 3) : ContDiff ℝ ∞ (V i) :=
    (he (latticeFrame a.cover hUD n i.1,i.2)).1
  refine ⟨hfin,coefficientJetGoodEvent_measurable V (oscillatorySeed S0 T0 n)
    hV (oscillatorySeed_contDiff S0 T0 hS0 hT0 n) n Ω _,?_⟩
  apply (coefficientJetGoodEvent_failure_le V (oscillatorySeed S0 T0 n) n Ω _).trans
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) :=
      add_le_add ((hcoeff n hn0 hfin).trans (ENNReal.ofReal_le_ofReal ht.le)) hjet
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ ε/2) (by linarith : 0 ≤ ε/2)]
      congr 1
      ring

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.LocalCompactWaveData.lattice_good_event_probability_oai := @OAI.Yau.Geometry.LocalCompactWaveData.lattice_good_event_probability_oai
