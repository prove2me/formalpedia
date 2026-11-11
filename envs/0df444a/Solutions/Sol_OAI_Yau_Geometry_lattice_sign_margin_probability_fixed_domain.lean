-- Prove2me | solution 1 for OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:28:43.559809+00:00
-- url     : https://prove2.me/submissions/93ec2f58-84d5-41a5-a1af-b69dde0d9d05

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
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_lattice_logarithmic_jet_estimates
import Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_lattice_sign_coefficient_upper
import Theorems.Thm_OAI_Yau_Geometry_lattice_actual_two_point_energy_fixed_domain

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

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_TwoPointCoefficientEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma pairLinearSum_real_combination (z w : ι → ℂ) (u v : ℝ) :
    pairLinearSum (fun i ↦ (u:ℂ)*z i+(v:ℂ)*w i) =
      fun a ↦ u*pairLinearSum z a+v*pairLinearSum w a := by
  classical
  funext a
  simp only [pairLinearSum,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

lemma complex_norm_add_sq_bound (z w : ℂ) : ‖z+w‖^2 ≤ 2*‖z‖^2+2*‖w‖^2 := by
  have hh := norm_add_le z w
  have hs := sq_le_sq₀ (norm_nonneg (z+w)) (add_nonneg (norm_nonneg z) (norm_nonneg w))
  have hh2 := hs.mpr hh
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

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

lemma pairJetMap_law (z : κ → ι → ℂ) :
    (gaussianPairs (ι := ι)).map (fun a ↦ pairJetMap z (WithLp.toLp 2 a)) =
      (stdGaussian (EuclideanSpace ℝ (ι × Fin 2))).map (pairJetMap z) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
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
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianFactorTwoSided
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
local notation "E" => EuclideanSpace ℝ ι

lemma exists_gaussian_factor_two_sided (T : F →L[ℝ] E) (a B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B)
    (hlo : ∀ v : E, a*‖v‖^2 ≤ ‖T.adjoint v‖^2)
    (hhi : ∀ v : E, ‖T.adjoint v‖^2 ≤ B^2*‖v‖^2) :
    ∃ L : E ≃L[ℝ] E,
      (stdGaussian F).map T = (stdGaussian E).map L ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt a)⁻¹ ∧ ‖L.toContinuousLinearMap‖ ≤ B := by
  let L := (LinearEquiv.ofBijective (covarianceFactor T).toLinearMap
    (covarianceFactor_bijective T a ha hlo)).toContinuousLinearEquiv
  refine ⟨L,gaussian_covariance_factorization T,?_,?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have hb := covarianceFactor_lower T a ha hlo (L.symm v)
    change Real.sqrt a*‖L.symm v‖ ≤ ‖L (L.symm v)‖ at hb
    rw [L.apply_symm_apply] at hb
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ (Real.sqrt_pos.mpr ha)).mpr (by simpa [mul_comm] using hb)
  · apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    change ‖covarianceFactor T v‖ ≤ B*‖v‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
    rw [covarianceFactor_norm_sq,mul_pow]
    exact hhi v

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianUniformBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma stdGaussian_open_positive : (stdGaussian E).IsOpenPosMeasure := by
  let : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:NNReal) ≠ 0)).isOpenPosMeasure
  rw [← map_pi_eq_stdGaussian]
  apply Continuous.isOpenPosMeasure_map (by fun_prop)
  exact (WithLp.equiv 2 (ι → ℝ)).symm.surjective

lemma uniform_gaussian_ball (R r : ℝ) (hr : 0 < r) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ z : E, ‖z‖ ≤ R → p ≤ stdGaussian E (ball z r) := by
  classical
  let : (stdGaussian E).IsOpenPosMeasure := stdGaussian_open_positive
  obtain ⟨s,hs⟩ := (isCompact_closedBall (0:E) R).elim_finite_subcover
    (fun z : E ↦ ball z (r/2)) (fun _ ↦ isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨z,mem_ball_self (by positivity)⟩)
  let p : ℝ≥0∞ := s.inf (fun z ↦ stdGaussian E (ball z (r/2)))
  have hp : 0 < p := by
    dsimp only [p]
    clear hs p
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
      rw [Finset.inf_insert]
      exact lt_min (measure_ball_pos _ _ (by positivity)) ih
  refine ⟨p,hp,?_⟩
  intro z hz
  have hz' : z ∈ closedBall (0:E) R := by simpa only [mem_closedBall,dist_zero_right] using hz
  obtain ⟨y,hy,hyz⟩ := mem_iUnion₂.mp (hs hz')
  apply (Finset.inf_le hy).trans
  apply measure_mono
  intro x hx
  have hx' : dist x y < r/2 := hx
  have hz'' : dist z y < r/2 := hyz
  have hh := dist_triangle x y z
  rw [dist_comm y z] at hh
  change dist x z < r
  linarith

lemma uniform_affine_gaussian_ball (A B M r : ℝ) (hA : 0 ≤ A)
    (hB : 0 < B) (hM : 0 ≤ M) (hr : 0 < r) (target : E) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ (L : E ≃L[ℝ] E) (mean : E),
      ‖L.symm.toContinuousLinearMap‖ ≤ A → ‖L.toContinuousLinearMap‖ ≤ B → ‖mean‖ ≤ M →
      p ≤ ((stdGaussian E).map (fun z ↦ mean+L z)) (ball target r) := by
  let radius : NNReal := ⟨A*(‖target‖+M), mul_nonneg hA (add_nonneg (norm_nonneg _) hM)⟩
  obtain ⟨p,hp,huniform⟩ := uniform_gaussian_ball (ι := ι) radius (r/B) (div_pos hr hB)
  refine ⟨p,hp,?_⟩
  intro L mean hLi hL hm
  let center := L.symm (target-mean)
  have hc : ‖center‖ ≤ A*(‖target‖+M) := by
    exact (L.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul hLi ((norm_sub_le _ _).trans (add_le_add le_rfl hm)) (norm_nonneg _) hA)
  apply (huniform center hc).trans
  rw [Measure.map_apply (by fun_prop) isOpen_ball.measurableSet]
  apply measure_mono
  intro z hz
  change dist (mean+L z) target < r
  rw [dist_eq_norm]
  have he : mean+L z-target = L (z-center) := by
    simp only [map_sub,center,L.apply_symm_apply]
    abel
  rw [he]
  have hb := L.toContinuousLinearMap.le_opNorm (z-center)
  have hh : ‖z-center‖ < r/B := by simpa only [mem_ball,dist_eq_norm] using hz
  have hmul := (lt_div_iff₀ hB).mp hh
  calc
    _ ≤ B*‖z-center‖ := hb.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
    _ < r := by nlinarith

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_TwoValueGaussianMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Probability MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma pairJetMap_two_inner (z w : ι → ℂ) (v : EuclideanSpace ℝ (Fin 2))
    (a : ι × Fin 2 → ℝ) :
    ⟪v,pairJetMap ![z,w] (WithLp.toLp 2 a)⟫ =
      pairLinearSum (fun i ↦ (v 0:ℂ)*z i+(v 1:ℂ)*w i) a := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,Fin.sum_univ_two,pairJetMap_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,pairLinearSum_real_combination]
  ring

lemma pairJetMap_two_energy (z w : ι → ℂ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖(pairJetMap ![z,w]).adjoint v‖^2 =
      ∑ i, ‖(v 0:ℂ)*z i+(v 1:ℂ)*w i‖^2 := by
  rw [← variance_gaussianMap_inner]
  simp_rw [pairJetMap_two_inner]
  exact variance_pairLinearSum _

lemma two_point_energy_upper (z w : ι → ℂ) (M : ℝ)
    (hz : ∑ i, ‖z i‖^2 ≤ M) (hw : ∑ i, ‖w i‖^2 ≤ M) (u v : ℝ) :
    (∑ i, ‖(u:ℂ)*z i+(v:ℂ)*w i‖^2) ≤ 2*M*(u^2+v^2) := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
    complex_norm_add_sq_bound ((u:ℂ)*z i) ((v:ℂ)*w i))
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Finset.sum_add_distrib,← Finset.mul_sum] at hh
  have hz' := mul_le_mul_of_nonneg_left hz (sq_nonneg u)
  have hw' := mul_le_mul_of_nonneg_left hw (sq_nonneg v)
  nlinarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_TwoValueSignProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Probability MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
local notation "E" => EuclideanSpace ℝ (Fin 2)

lemma two_value_sign_probability (d M : ℝ) (hd : 0 < d) (hM : 0 ≤ M) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ {ι : Type} [Fintype ι] (z w : ι → ℂ) (mean : E),
      ‖mean‖ ≤ M → (∑ i, ‖z i‖^2) ≤ 4 → (∑ i, ‖w i‖^2) ≤ 4 →
      (∀ u v : ℝ, d*(u^2+v^2) ≤ ∑ i, ‖(u:ℂ)*z i+(v:ℂ)*w i‖^2) →
      p ≤ gaussianPairs {a | 1 ≤ mean 0+pairLinearSum z a ∧ mean 1+pairLinearSum w a ≤ -1} := by
  let target : E := WithLp.toLp 2 ![2,-2]
  obtain ⟨p,hp,hball⟩ := uniform_affine_gaussian_ball (ι := Fin 2) (Real.sqrt d)⁻¹ 4 M 1
    (by positivity) (by norm_num) hM (by norm_num) target
  refine ⟨p,hp,?_⟩
  intro ι hfin z w mean hm hz hw hgap
  let T := pairJetMap ![z,w]
  have hlo (v : E) : d*‖v‖^2 ≤ ‖T.adjoint v‖^2 := by
    rw [pairJetMap_two_energy]
    simpa only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two] using hgap (v 0) (v 1)
  have hhi (v : E) : ‖T.adjoint v‖^2 ≤ (4:ℝ)^2*‖v‖^2 := by
    rw [pairJetMap_two_energy]
    have hh := two_point_energy_upper z w 4 hz hw (v 0) (v 1)
    have hn : ‖v‖^2 = (v 0)^2+(v 1)^2 := by rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
    rw [hn]
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]
  obtain ⟨L,hLaw,hLi,hL⟩ := exists_gaussian_factor_two_sided T d 4 hd (by norm_num) hlo hhi
  have hmap : gaussianPairs.map (fun a ↦ mean+T (WithLp.toLp 2 a)) =
      (stdGaussian E).map (fun v ↦ mean+L v) := by
    have hh := congrArg (fun μ : Measure E ↦ μ.map (fun v ↦ mean+v)) (pairJetMap_law ![z,w])
    rw [hLaw] at hh
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)] at hh
    exact hh
  have hb := hball L mean hLi hL hm
  rw [← hmap,Measure.map_apply (by fun_prop) isOpen_ball.measurableSet] at hb
  apply hb.trans (measure_mono ?_)
  intro a ha
  let y := mean+T (WithLp.toLp 2 a)
  have hn : ‖y-target‖ < 1 := by simpa only [mem_preimage,mem_ball,dist_eq_norm] using ha
  have h0 := (PiLp.norm_apply_le (y-target) 0).trans_lt hn
  have h1 := (PiLp.norm_apply_le (y-target) 1).trans_lt hn
  change |y 0-2| < 1 at h0
  change |y 1-(-2)| < 1 at h1
  have hy0 : y 0 = mean 0+pairLinearSum z a := by simp [y,T,pairJetMap_apply]
  have hy1 : y 1 = mean 1+pairLinearSum w a := by simp [y,T,pairJetMap_apply]
  change 1 ≤ mean 0+pairLinearSum z a ∧ mean 1+pairLinearSum w a ≤ -1
  rw [← hy0,← hy1]
  exact ⟨by linarith [(abs_lt.mp h0).1],by linarith [(abs_lt.mp h1).2]⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FixedDomainLatticeSignMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section

theorem lattice_sign_margin_probability_fixed_domain_oai
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) {H : Set _root_.OAI.Yau.Jets.Coord}
    (hH : IsCompact H) (hg : ContinuousOn g H)
    (hp : ∀ y ∈ H, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1/4 ∧ ∃ p : ℝ≥0∞, 0 < p ∧
      ∀ (w S S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (D U Q : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ)
        (a : LocalCompactWaveData g w S D m J K k0) (_ : IsCompact D) (_ : D ⊆ H) (hUD : U ⊆ D),
        U ⊆ H → IsOpen U → Bornology.IsBounded U → IsCompact Q → Q ⊆ U →
        ContDiff ℝ ∞ S → ContDiff ℝ ∞ S0 → ContDiff ℝ ∞ T0 →
        ∀ gamma > 0, (∀ x ∈ Q, S0 x+gamma ≤ S x) →
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), letI := hfin
          ∀ x ∈ Q, ∃ j : Fin 4,
            let F := rescaledGaussianField
              (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
              S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
            p ≤ gaussianPairs {coeff | 1 ≤ F coeff 0 ∧ F coeff (tau • Pi.single j 1) ≤ -1} := by
  obtain ⟨tau,ht,ht4,d,hd,henergy⟩ := lattice_actual_two_point_energy_fixed_domain g hH hg hp
  obtain ⟨p,hp,hprob⟩ := two_value_sign_probability d 2 hd (by norm_num)
  refine ⟨tau,ht,ht4,p,hp,?_⟩
  intro w S S0 T0 D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS hS0 hT0 gamma hgamma hgap
  filter_upwards [henergy w S D U Q m J K k0 a hD hDH hUD hUH hU hUb hQ hQU hS,
    a.lattice_sign_coefficient_upper hUD hU hUb hQ hQU hS,
    a.sign_scale_seed_decay hUD hU hUb hQ hQU hS S0 T0 hS0 hT0 gamma hgamma hgap 0 1 (by norm_num)]
    with n he hu hs
  obtain ⟨hfin,he⟩ := he
  obtain ⟨hfin',hu⟩ := hu
  obtain ⟨hfin'',hs⟩ := hs
  have heq : hfin' = hfin := Subsingleton.elim _ _
  have heq' : hfin'' = hfin := Subsingleton.elim _ _
  subst hfin'
  subst hfin''
  let := hfin
  refine ⟨hfin,?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := he x hx
  let v : _root_.OAI.Yau.Jets.Coord := tau • Pi.single j 1
  let seed := rescaledSeed S0 T0 S n (sourceSignScale g S x) (a.latticeSigma hUD n x) x
  let A := fun i : SourceGrid U n × Fin 3 ↦ normalizedRescaling
    (latticeWave a.cover a.beams hUD n i.1 i.2) S n (sourceSignScale g S x)
    (a.latticeSigma hUD n x) x
  let mean : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![seed 0,seed v]
  have hvnorm : ‖v‖ = tau := by
    simp [v,norm_smul,Real.norm_eq_abs,abs_of_pos ht,Pi.norm_single]
  have hv : sourceEuclideanNorm v ≤ 2 := (sourceEuclideanNorm_le v).trans (by rw [hvnorm]; linarith)
  have hv0 : sourceEuclideanNorm (0:_root_.OAI.Yau.Jets.Coord) ≤ 2 := by simp [sourceEuclideanNorm]
  have hs0 := hs x hx 0 hv0 (0 : Fin 1)
  have hs1 := hs x hx v hv (0 : Fin 1)
  simp only [Fin.val_zero,norm_iteratedFDeriv_zero] at hs0 hs1
  change ‖seed 0‖ ≤ 1 at hs0
  change ‖seed v‖ ≤ 1 at hs1
  have hmean : ‖mean‖ ≤ 2 := by
    have hsq : ‖mean‖^2 = (seed 0)^2+(seed v)^2 := by
      simp [mean,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
    have h0 := pow_le_pow_left₀ (norm_nonneg _) hs0 2
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hs1 2
    simp only [Real.norm_eq_abs,sq_abs,one_pow] at h0 h1
    nlinarith [norm_nonneg mean]
  have hb := hprob (fun i ↦ A i 0) (fun i ↦ A i v) mean hmean
    (hu x hx 0 (by simp)) (hu x hx v (by rw [hvnorm]; linarith)) hj
  refine ⟨j,?_⟩
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext coeff
  simp [rescaledGaussianField_decomposition,mean,seed,A,v,
    pairLinearSum_eq_complex,gaussianWaveField,Complex.re_sum]

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain_oai := @OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain_oai
