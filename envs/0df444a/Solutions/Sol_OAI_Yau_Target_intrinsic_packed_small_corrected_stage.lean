-- Prove2me | solution 1 for OAI.Yau.Target.intrinsic_packed_small_corrected_stage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:32:37.812854+00:00
-- url     : https://prove2.me/submissions/601d7b99-c88c-4e81-add6-def62a441de5

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
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.OperatorNorm
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
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004
import Theorems.Thm_OAI_Yau_Target_intrinsic_packed_selected_stage

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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_r5678c9_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
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

local instance instFactEqNatFinrankRealSeedAmbientHAddOfNat_1_r5678c9_1 : Fact (Module.finrank ℝ SeedAmbient = 4+1) := ⟨by simp [SeedAmbient]⟩
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
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CompactResidualMultiplier
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

lemma compact_scalar_derivativeBound (f : _root_.OAI.Yau.Jets.Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ C > 0, ∀ x ∈ Q, DerivativeBound k f x C := by
  have hb (j : Fin (k+1)) : ∃ C > 0, ∀ x ∈ Q, ‖iteratedFDeriv ℝ j.val f x‖ ≤ C := by
    have hc : Continuous (iteratedFDeriv ℝ j.val f) := hf.continuous_iteratedFDeriv
      (by exact_mod_cast (show (j.val:ℕ∞) ≤ ⊤ from le_top))
    obtain ⟨C,hC,h⟩ := (hQ.image hc).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx ↦ h _ ⟨x,hx,rfl⟩⟩
  choose C hC hb using hb
  refine ⟨∑ j, C j,?_,?_⟩
  · exact (hC ⟨0,by omega⟩).trans_le
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))
  · intro x hx j hj
    exact (hb ⟨j,by omega⟩ x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))

lemma product_tsupport_subset_right (f R : _root_.OAI.Yau.Jets.Coord → ℂ) :
    tsupport (fun x ↦ f x*R x) ⊆ tsupport R := by
  apply closure_mono
  intro x hx hz
  exact hx (by simp [hz])

theorem compact_residual_multiplier (f : _root_.OAI.Yau.Jets.Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ B > 0, ∀ (R : _root_.OAI.Yau.Jets.Coord → ℂ), ContDiff ℝ ∞ R → tsupport R ⊆ Q →
      ContDiff ℝ ∞ (fun x ↦ f x*R x) ∧
      tsupport (fun x ↦ f x*R x) ⊆ Q ∧
      ∀ (H : _root_.OAI.Yau.Jets.Coord → ℝ), (∀ x, 0 ≤ H x) →
        (∀ x, DerivativeBound k R x (H x)) →
        ∀ x, DerivativeBound k (fun z ↦ f z*R z) x (B*H x) := by
  obtain ⟨C,hC,hbound⟩ := compact_scalar_derivativeBound f hf hQ k
  refine ⟨2^k*C,by positivity,?_⟩
  intro R hR hRQ
  have hprod := (product_tsupport_subset_right f R).trans hRQ
  refine ⟨hf.mul hR,hprod,?_⟩
  intro H hH hb x
  by_cases hx : x ∈ Q
  · exact DerivativeBound.mul hf hR hC.le (hH x) (hbound x hx) (hb x)
  · intro j hj
    rw [iteratedFDeriv_zero_off_tsupport hprod hx j,norm_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hC.le) (hH x)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CorrectionAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau

theorem exact_correction {u lam s residual d : ℝ} (hlam : lam ≠ 0)
    (hden : s + lam * u ^ 2 ≠ 0) :
    let f := residual / (s + lam * u ^ 2)
    (u * d + f * s) + lam * (f * u - lam⁻¹ * d) * u = residual := by
  dsimp
  have hc (f : ℝ) : (u * d + f * s) +
      lam * (f * u - lam⁻¹ * d) * u = f * (s + lam * u ^ 2) := by
    field_simp [hlam]
    ring
  rw [hc, div_mul_cancel₀ _ hden]

theorem first_jet_coercivity {a b n lam : ℝ} (hn : 0 < n)
    (hlam : n ^ 2 ≤ lam) :
    (n ^ 2 / 2) * (a + b / n) ^ 2 ≤ b ^ 2 + lam * a ^ 2 := by
  have h := sq_nonneg (n * a - b)
  have ha := mul_nonneg (sub_nonneg.mpr hlam) (sq_nonneg a)
  field_simp
  nlinarith

end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoordinateCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
variable {n : ℕ}

theorem coordDiv_mul {u : Coord n → ℝ} {V : Coord n → Coord n} {x : Coord n}
    (hu : DifferentiableAt ℝ u x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    coordDiv (fun y i ↦ u y * V y i) x =
      u x * coordDiv V x + pairing u V x := by
  unfold coordDiv pairing coordPartial
  simp_rw [fderiv_fun_mul hu (hV _)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedDiv_mul {gamma u : Coord n → ℝ} {V : Coord n → Coord n}
    {x : Coord n} (hg : DifferentiableAt ℝ gamma x) (hgn : gamma x ≠ 0)
    (hu : DifferentiableAt ℝ u x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x) :
    weightedDiv gamma (fun y i ↦ u y * V y i) x =
      u x * weightedDiv gamma V x + pairing u V x := by
  have heq : (fun y i ↦ gamma y * (u y * V y i)) =
      (fun y i ↦ u y * (gamma y * V y i)) := by
    funext y i
    ring
  unfold weightedDiv
  rw [heq, coordDiv_mul (V := fun y i ↦ gamma y * V y i) hu (fun i ↦ hg.mul (hV i))]
  have hp : pairing u (fun y i ↦ gamma y * V y i) x = gamma x * pairing u V x := by
    unfold pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp]
  field_simp

theorem weighted_exact_correction {gamma u f : Coord n → ℝ}
    {V : Coord n → Coord n} {x : Coord n} {lam residual : ℝ}
    (hg : DifferentiableAt ℝ gamma x) (hgn : gamma x ≠ 0)
    (hu : DifferentiableAt ℝ u x) (hf : DifferentiableAt ℝ f x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y ↦ V y i) x)
    (hlam : lam ≠ 0) (hden : pairing u V x + lam * u x ^ 2 ≠ 0)
    (hfval : f x = residual / (pairing u V x + lam * u x ^ 2)) :
    weightedDiv gamma (fun y i ↦ u y * (f y * V y i)) x +
      lam * (f x * u x - lam⁻¹ *
        weightedDiv gamma (fun y i ↦ f y * V y i) x) * u x = residual := by
  rw [weightedDiv_mul (V := fun y i ↦ f y * V y i) hg hgn hu (fun i ↦ hf.mul (hV i))]
  have hp : pairing u (fun y i ↦ f y * V y i) x = f x * pairing u V x := by
    unfold pairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp, hfval]
  exact exact_correction hlam hden

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ReciprocalDerivativeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Filter
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem reciprocal_derivative_bound (r : ℕ) :
    ∃ C > 0, ∀ (f : E → ℝ), ContDiff ℝ ∞ f → ∀ (x : E), f x ≠ 0 →
      ∀ (B : ℝ), 0 ≤ B →
      (∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ |f x| *B^i) →
      ‖iteratedFDeriv ℝ r (fun y ↦ (f y)⁻¹) x‖ ≤ C*|f x|⁻¹*B^r := by
  let C : ℝ := 1 + ∑ i ∈ Finset.range (r+1), ‖iteratedFDeriv ℝ i (fun t : ℝ ↦ t⁻¹) 1‖
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨(r.factorial:ℝ)*C, mul_pos (by positivity) hC, ?_⟩
  intro f hf x hx B hB hb
  let F : E → ℝ := fun y ↦ (f x)⁻¹ * f y
  have hF : ContDiff ℝ ∞ F := contDiff_const.mul hf
  have hFx : F x = 1 := by simp [F,hx]
  let s : Set E := F ⁻¹' Ioi 0
  have hs : IsOpen s := isOpen_Ioi.preimage hF.continuous
  have hxs : x ∈ s := by simp [s,hFx]
  have hinv : ContDiffOn ℝ ∞ (fun t : ℝ ↦ t⁻¹) (Ioi 0) :=
    contDiffOn_id.inv (fun t ht ↦ ne_of_gt ht)
  have hi (i : ℕ) : iteratedFDerivWithin ℝ i (fun t : ℝ ↦ t⁻¹) (Ioi 0) (F x) =
      iteratedFDeriv ℝ i (fun t : ℝ ↦ t⁻¹) 1 := by
    rw [hFx, iteratedFDerivWithin_of_isOpen i isOpen_Ioi (by norm_num : (1:ℝ) ∈ Ioi 0)]
  have hbF (i : ℕ) (hi1 : 1 ≤ i) (hir : i ≤ r) :
      ‖iteratedFDerivWithin ℝ i F s x‖ ≤ B^i := by
    rw [iteratedFDerivWithin_of_isOpen i hs hxs]
    change ‖iteratedFDeriv ℝ i ((f x)⁻¹ • f) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (hf.of_le (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_inv]
    calc
      |f x|⁻¹ * ‖iteratedFDeriv ℝ i f x‖ ≤ |f x|⁻¹ * (|f x| *B^i) :=
        mul_le_mul_of_nonneg_left (hb i hi1 hir) (by positivity)
      _ = B^i := by rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hx), one_mul]
  have hcF (i : ℕ) (hir : i ≤ r) :
      ‖iteratedFDerivWithin ℝ i (fun t : ℝ ↦ t⁻¹) (Ioi 0) (F x)‖ ≤ C := by
    rw [hi]
    have h := Finset.single_le_sum (fun j _ ↦ norm_nonneg
      (iteratedFDeriv ℝ j (fun t : ℝ ↦ t⁻¹) 1))
      (Finset.mem_range.mpr (show i < r+1 by omega))
    dsimp [C]
    linarith
  have hcomp := norm_iteratedFDerivWithin_comp_le hinv hF.contDiffOn (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top)) isOpen_Ioi.uniqueDiffOn hs.uniqueDiffOn
    (show MapsTo F s (Ioi 0) from fun _ hy ↦ hy) hxs hcF hbF
  rw [iteratedFDerivWithin_of_isOpen r hs hxs] at hcomp
  have hg : (fun y ↦ (f y)⁻¹) = (f x)⁻¹ • ((fun t : ℝ ↦ t⁻¹) ∘ F) := by
    funext y
    simp [F,mul_inv_rev,hx,mul_comm]
  have hlocal : ContDiffAt ℝ (r:ℕ∞ω) ((fun t : ℝ ↦ t⁻¹) ∘ F) x :=
    ((hinv.contDiffAt (isOpen_Ioi.mem_nhds (by rw [hFx]; norm_num))).comp x
      hF.contDiffAt).of_le (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))
  rw [hg,iteratedFDeriv_const_smul_apply hlocal,norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    _ ≤ |f x|⁻¹ * ((r.factorial:ℝ)*C*B^r) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FrequencyLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma frequency_product_derivative (f g : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : E) (r a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(r+a+b)*(H*K) := by
  refine (norm_iteratedFDeriv_mul_le hf hg x
    (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)*(A*N^(i+a)*H)*
        (B*N^(r-i+b)*K) := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i ≤ r := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfb i hir) (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg hA (pow_nonneg hN _)) hH))
        (hgb (r-i) (by omega))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg (mul_nonneg hB (pow_nonneg hN _)) hK)
    _ = (∑ i ∈ Finset.range (r+1), (r.choose i:ℝ))*(A*B*N^(r+a+b)*(H*K)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
      have hp : N^(i+a)*N^(r-i+b) = N^(r+a+b) := by rw [← pow_add]; congr 1; omega
      calc
        _ = (r.choose i:ℝ)*(A*B*(N^(i+a)*N^(r-i+b))*(H*K)) := by ring
        _ = _ := by rw [hp]
    _ = _ := by
      have hc : (∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)) = (2:ℝ)^r := by
        exact_mod_cast (Nat.sum_range_choose r)
      rw [hc]
      ring

lemma compact_real_derivative_bound (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    {Q : Set E} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ i, i ≤ r → ∀ x ∈ Q, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hb (i : Fin (r+1)) : ∃ C > 0, ∀ x ∈ Q, ‖iteratedFDeriv ℝ i.val f x‖ ≤ C := by
    obtain ⟨C,hC,hb⟩ := (hQ.image (hf.continuous_iteratedFDeriv
      (by exact_mod_cast (show (i.val:ℕ∞) ≤ ⊤ from le_top)))).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx ↦ hb _ ⟨x,hx,rfl⟩⟩
  choose c hc hbound using hb
  have hp : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ (hc i).le)
  refine ⟨1+∑ i, c i,by linarith,?_⟩
  intro i hi x hx
  have hsum := Finset.single_le_sum (fun j _ ↦ (hc j).le)
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (r+1)))
  exact (hbound ⟨i,by omega⟩ x hx).trans (by linarith)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalFrequencyLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma frequency_product_derivative_on (f g : E → ℝ) {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g U) (x : E) (hx : x ∈ U) (r a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (_ : 0 ≤ B) (hH : 0 ≤ H) (_ : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(r+a+b)*(H*K) := by
  have hprod := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx
    (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hprod
  refine hprod.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)*(A*N^(i+a)*H)*
        (B*N^(r-i+b)*K) := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i ≤ r := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      gcongr
      · exact hfb i hir
      · exact hgb (r-i) (by omega)
    _ = (∑ i ∈ Finset.range (r+1), (r.choose i:ℝ))*(A*B*N^(r+a+b)*(H*K)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
      have hp : N^(i+a)*N^(r-i+b) = N^(r+a+b) := by rw [← pow_add]; congr 1; omega
      calc
        _ = (r.choose i:ℝ)*(A*B*(N^(i+a)*N^(r-i+b))*(H*K)) := by ring
        _ = _ := by rw [hp]
    _ = _ := by
      have hc : (∑ i ∈ Finset.range (r+1), (r.choose i:ℝ)) = (2:ℝ)^r := by
        exact_mod_cast (Nat.sum_range_choose r)
      rw [hc]
      ring

lemma scaled_frequency_product_on (f g : E → ℝ) {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (x : E) (hx : x ∈ U)
    (r s a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(s*i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(s*i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(s*r+a+b)*(H*K) := by
  have hf' (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ (A*N^a)*(N^s)^(i+0)*H := by
    convert hfb i hi using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.add_zero,pow_add,← pow_mul]
    ring
  have hg' (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i g x‖ ≤ (B*N^b)*(N^s)^(i+0)*K := by
    convert hgb i hi using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.add_zero,pow_add,← pow_mul]
    ring
  have h := frequency_product_derivative_on f g hU hf hg x hx r 0 0
    (by positivity) (by positivity) (by positivity) hH hK hf' hg'
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.add_zero,pow_add,← pow_mul]
  ring

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
open Function Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem quotient_tsupport_subset (R D : E → ℝ) :
    tsupport (fun x ↦ R x / D x) ⊆ tsupport R := by
  apply closure_mono
  intro x hx
  simp only [mem_support] at *
  intro h
  exact hx (by simp [h])

theorem smooth_quotient_on_residual_support {R D : E → ℝ} {n : ℕ∞ω}
    (hR : ContDiff ℝ n R) (hD : ContDiff ℝ n D)
    (hn : ∀ x ∈ tsupport R, D x ≠ 0) :
    ContDiff ℝ n (fun x ↦ R x / D x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport R
  · exact hR.contDiffAt.div hD.contDiffAt (hn x hx)
  · have he : R =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

omit [NormedSpace ℝ E] in
theorem quotient_compact_support {R D : E → ℝ} (hR : HasCompactSupport R) :
    HasCompactSupport (fun x ↦ R x / D x) := by
  exact hR.of_isClosed_subset isClosed_closure (quotient_tsupport_subset R D)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GlobalCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
open Function Set
open scoped ContDiff
variable {n : ℕ}

theorem pairing_smooth {u : Coord n → ℝ} {V : Coord n → Coord n}
    (hu : ContDiff ℝ ∞ u) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    ContDiff ℝ ∞ (pairing u V) := by
  apply ContDiff.sum
  intro i _
  exact ((hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).mul (hV i)

theorem correctionDenominator_smooth {u : Coord n → ℝ} {V : Coord n → Coord n}
    (hu : ContDiff ℝ ∞ u) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (lam : ℝ) :
    ContDiff ℝ ∞ (correctionDenominator u V lam) :=
  (pairing_smooth hu hV).add (contDiff_const.mul (hu.pow 2))

theorem global_exact_correction {gamma u R : Coord n → ℝ} {V : Coord n → Coord n}
    {lam : ℝ} (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hu : ContDiff ℝ ∞ u) (hR : ContDiff ℝ ∞ R) (hcompact : HasCompactSupport R)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (hlam : lam ≠ 0)
    (hden : ∀ x ∈ tsupport R, correctionDenominator u V lam x ≠ 0) :
    ∃ f : Coord n → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ tsupport R ∧
      (∀ x, f x = R x / correctionDenominator u V lam x) ∧
      ∀ x, weightedDiv gamma (fun y i ↦ u y * (f y * V y i)) x +
        lam * (f x * u x - lam⁻¹ *
          weightedDiv gamma (fun y i ↦ f y * V y i) x) * u x = R x := by
  let D := correctionDenominator u V lam
  let f := fun x ↦ R x / D x
  have hf : ContDiff ℝ ∞ f :=
    smooth_quotient_on_residual_support hR (correctionDenominator_smooth hu hV lam) hden
  refine ⟨f, hf, quotient_compact_support hcompact,
    quotient_tsupport_subset R D, fun _ ↦ rfl, ?_⟩
  intro x
  by_cases hx : D x ≠ 0
  · exact weighted_exact_correction (hg.differentiable (by simp)).differentiableAt (hgn x)
      (hu.differentiable (by simp)).differentiableAt (hf.differentiable (by simp)).differentiableAt
      (fun i ↦ ((hV i).differentiable (by simp)).differentiableAt) hlam hx rfl
  · have hRx : R x = 0 := by
      by_contra hr
      exact hx (hden x (subset_closure hr))
    have hfx : f x = 0 := by simp [f, hRx]
    rw [weightedDiv_mul (V := fun y i ↦ f y * V y i)
      (hg.differentiable (by simp)).differentiableAt (hgn x) (hu.differentiable (by simp)).differentiableAt
      (fun i ↦ (hf.differentiable (by simp)).differentiableAt.mul
        ((hV i).differentiable (by simp)).differentiableAt)]
    have hp : pairing u (fun y i ↦ f y * V y i) x = 0 := by simp [pairing, hfx]
    rw [hp, hfx, hRx]
    field_simp [hlam]
    ring

theorem weightedDiv_smooth {gamma : Coord n → ℝ} {V : Coord n → Coord n}
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    ContDiff ℝ ∞ (weightedDiv gamma V) := by
  apply (hg.inv hgn).mul
  apply ContDiff.sum
  intro i _
  exact (((hg.mul (hV i)).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

theorem densityCorrection_smooth {gamma u f : Coord n → ℝ} {V : Coord n → Coord n}
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (lam : ℝ) :
    ContDiff ℝ ∞ (densityCorrection gamma u f V lam) :=
  (hf.mul hu).sub (contDiff_const.mul
    (weightedDiv_smooth hg hgn (fun i ↦ hf.mul (hV i))))

theorem weightedDiv_zero_off_support (gamma f : Coord n → ℝ)
    (V : Coord n → Coord n) {x : Coord n} (hx : x ∉ tsupport f) :
    weightedDiv gamma (fun y i ↦ f y * V y i) x = 0 := by
  have he : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have hd (i : Fin n) :
      fderiv ℝ (fun y ↦ gamma y * (f y * V y i)) x = 0 := by
    have heq : (fun y ↦ gamma y * (f y * V y i)) =ᶠ[nhds x] (fun _ ↦ 0) := by
      filter_upwards [he] with y hy
      simp [hy]
    rw [heq.fderiv_eq]
    simp
  simp [weightedDiv, coordDiv, coordPartial, hd]

theorem densityCorrection_tsupport_subset (gamma u f : Coord n → ℝ)
    (V : Coord n → Coord n) (lam : ℝ) :
    tsupport (densityCorrection gamma u f V lam) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra h
  have hf0 := image_eq_zero_of_notMem_tsupport h
  have hd0 := weightedDiv_zero_off_support gamma f V h
  exact hx (by simp [densityCorrection, hf0, hd0])

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RoundCoordinateGradient
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma roundCoordFactor_ge_one (x : Yau.Jets.Coord) : 1 ≤ roundCoordFactor x := by
  unfold roundCoordFactor
  nlinarith [sq_nonneg (‖seedCoordEquiv x‖)]

lemma roundCoordFactor_smooth : ContDiff ℝ ∞ roundCoordFactor := by
  unfold roundCoordFactor
  exact ((((contDiff_norm_sq ℝ).comp seedCoordEquiv.contDiff).add contDiff_const).div_const 4).pow 2

lemma roundCoordGradient_smooth (u : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (roundCoordGradient u) := by
  apply contDiff_pi.mpr
  intro i
  exact roundCoordFactor_smooth.mul ((hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

lemma roundCoordGradient_pairing (u : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    Yau.pairing u (roundCoordGradient u) x =
      roundCoordFactor x * (sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1)))^2 := by
  rw [sourceEuclideanNorm,Real.sq_sqrt (by positivity),Finset.mul_sum]
  unfold Yau.pairing Yau.coordPartial
  apply Finset.sum_congr rfl
  intro i _
  dsimp [roundCoordGradient]
  ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RoundCorrectionDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

lemma roundCorrectionDenominator_formula (u : Yau.Jets.Coord → ℝ) (n : ℕ) (x : Yau.Jets.Coord) :
    roundCorrectionDenominator u n x =
      roundCoordFactor x*(sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1)))^2 +
      seedEigenvalue n*(u x)^2 := by
  unfold roundCorrectionDenominator Yau.correctionDenominator
  rw [roundCoordGradient_pairing]

lemma roundCorrectionDenominator_smooth (u : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ContDiff ℝ ∞ (roundCorrectionDenominator u n) :=
  Yau.correctionDenominator_smooth hu
    (fun i ↦ (contDiff_pi.mp (roundCoordGradient_smooth u hu)) i) _

lemma roundCorrectionDenominator_coercive (u : Yau.Jets.Coord → ℝ) {n : ℕ} (hn : 0 < n) (x : Yau.Jets.Coord) :
    ((n:ℝ)^2/2)*(sourceFirstJetSize u n x)^2 ≤ roundCorrectionDenominator u n x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hlam : (n:ℝ)^2 ≤ seedEigenvalue n := by
    unfold seedEigenvalue
    nlinarith
  have h := Yau.first_jet_coercivity (a := |u x|)
    (b := sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1))) hn' hlam
  rw [sq_abs] at h
  have he : sourceFirstJetSize u n x = |u x|+
      sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1))/(n:ℝ) := by
    simp only [sourceFirstJetSize,div_eq_mul_inv,mul_comm]
  rw [he,roundCorrectionDenominator_formula]
  have hp := mul_le_mul_of_nonneg_right (roundCoordFactor_ge_one x)
    (sq_nonneg (sourceEuclideanNorm (fun i ↦ fderiv ℝ u x (Pi.single i 1))))
  nlinarith

lemma roundCorrectionDenominator_lower (u : Yau.Jets.Coord → ℝ) {n : ℕ} (hn : 0 < n)
    (x : Yau.Jets.Coord) {H : ℝ} (hH : 0 < H)
    (hjet : ((n:ℝ)^65)⁻¹*H ≤ sourceFirstJetSize u n x) :
    (1/2:ℝ)*((n:ℝ)^128)⁻¹*H^2 ≤ roundCorrectionDenominator u n x := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hj0 : 0 ≤ ((n:ℝ)^65)⁻¹*H := by positivity
  have hj := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hj0 hjet 2)
    (by positivity : 0 ≤ (n:ℝ)^2/2)
  have he : ((n:ℝ)^2/2)*(((n:ℝ)^65)⁻¹*H)^2 = (1/2:ℝ)*((n:ℝ)^128)⁻¹*H^2 := by
    field_simp
  rw [he] at hj
  exact hj.trans (roundCorrectionDenominator_coercive u hn x)

lemma roundCorrectionDenominator_pos (u : Yau.Jets.Coord → ℝ) {n : ℕ} (hn : 0 < n)
    (x : Yau.Jets.Coord) {H : ℝ} (hH : 0 < H)
    (hjet : ((n:ℝ)^65)⁻¹*H ≤ sourceFirstJetSize u n x) :
    0 < roundCorrectionDenominator u n x :=
  lt_of_lt_of_le (by positivity) (roundCorrectionDenominator_lower u hn x hH hjet)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RoundDenominatorDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

lemma real_partial_iterated_bound (u : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u)
    (x : Yau.Jets.Coord) (i : Fin 4) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ u y (Pi.single i 1)) x‖ ≤
      ‖iteratedFDeriv ℝ (r+1) u x‖ := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h := norm_iteratedFDeriv_clm_apply_const (n := r)
    hdf.contDiffAt
    (c := Pi.single i (1:ℝ)) (x := x)
    (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))
  simpa [Pi.norm_single,norm_iteratedFDeriv_fderiv] using h

lemma roundDenominator_sum (u : Yau.Jets.Coord → ℝ) (n : ℕ) :
    roundCorrectionDenominator u n = fun x ↦
      (∑ i : Fin 4, roundCoordFactor x *
        (fderiv ℝ u x (Pi.single i 1)*fderiv ℝ u x (Pi.single i 1))) +
      seedEigenvalue n*(u x*u x) := by
  funext x
  rw [roundCorrectionDenominator_formula,sourceEuclideanNorm,
    Real.sq_sqrt (by positivity),Finset.mul_sum]
  simp [pow_two]

theorem round_denominator_derivative_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ∀ (n : ℕ), 0 < n →
      ∀ (x : Yau.Jets.Coord), x ∈ Q → ∀ (H : ℝ), 0 < H →
      (∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H) →
      ‖iteratedFDeriv ℝ r (roundCorrectionDenominator u n) x‖ ≤
        C*(n:ℝ)^(r+8)*H^2 := by
  obtain ⟨B,hB,hq⟩ := compact_real_derivative_bound roundCoordFactor roundCoordFactor_smooth hQ r
  let C : ℝ := 4*((2:ℝ)^r*B*((2:ℝ)^r*A*A))+10*((2:ℝ)^r*A*A)
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  intro u hu n hn x hx H hH hub
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0:ℝ) ≤ n := by positivity
  let p : Fin 4 → Yau.Jets.Coord → ℝ := fun i y ↦ fderiv ℝ u y (Pi.single i 1)
  have hp (i : Fin 4) : ContDiff ℝ ∞ (p i) :=
    (hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hpb (i : Fin 4) (k : ℕ) (hk : k ≤ r) :
      ‖iteratedFDeriv ℝ k (p i) x‖ ≤ A*(n:ℝ)^(k+4)*H := by
    exact (real_partial_iterated_bound u hu x i k).trans (by
      simpa [Nat.add_assoc] using hub (k+1) (by omega))
  have hsquare (i : Fin 4) (k : ℕ) (hk : k ≤ r) :
      ‖iteratedFDeriv ℝ k (fun y ↦ p i y*p i y) x‖ ≤
        ((2:ℝ)^r*A*A)*(n:ℝ)^(k+8)*(H^2) := by
    have h := frequency_product_derivative (p i) (p i) (hp i) (hp i) x k 4 4
      hN0 hA.le hA.le hH.le hH.le (fun j hj ↦ hpb i j (by omega))
      (fun j hj ↦ hpb i j (by omega))
    simp only [Nat.add_assoc,show 4+4=8 from rfl] at h
    have hh : H*H = H^2 := by ring
    rw [hh] at h
    exact h.trans (by gcongr; norm_num)
  have hqN (k : ℕ) (hk : k ≤ r) :
      ‖iteratedFDeriv ℝ k roundCoordFactor x‖ ≤ B*(n:ℝ)^(k+0)*1 := by
    have hpow : 1 ≤ (n:ℝ)^k := one_le_pow₀ hN
    simpa using (hq k hk x hx).trans (le_mul_of_one_le_right hB.le hpow)
  have hterm (i : Fin 4) :
      ‖iteratedFDeriv ℝ r (fun y ↦ roundCoordFactor y*(p i y*p i y)) x‖ ≤
        ((2:ℝ)^r*B*((2:ℝ)^r*A*A))*(n:ℝ)^(r+8)*H^2 := by
    have h := frequency_product_derivative roundCoordFactor (fun y ↦ p i y*p i y)
      roundCoordFactor_smooth ((hp i).mul (hp i)) x r 0 8
      hN0 hB.le (by positivity) (by norm_num : (0:ℝ) ≤ 1) (sq_nonneg H)
      hqN (hsquare i)
    simpa using h
  have hsum :
      ‖iteratedFDeriv ℝ r (fun y ↦ ∑ i : Fin 4, roundCoordFactor y*(p i y*p i y)) x‖ ≤
        4*((2:ℝ)^r*B*((2:ℝ)^r*A*A))*(n:ℝ)^(r+8)*H^2 := by
    rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
      ((roundCoordFactor_smooth.mul ((hp i).mul (hp i))).of_le
        (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
    have h := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun i _ ↦ hterm i))
    simpa [mul_assoc] using h
  have hu2 := frequency_product_derivative u u hu hu x r 3 3
    hN0 hA.le hA.le hH.le hH.le (fun j hj ↦ hub j (by omega))
    (fun j hj ↦ hub j (by omega))
  have hlam : 0 ≤ seedEigenvalue n := by unfold seedEigenvalue; positivity
  have hlam10 : seedEigenvalue n ≤ 10*(n:ℝ)^2 := by
    unfold seedEigenvalue
    have : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith
    nlinarith
  have heigen : ‖iteratedFDeriv ℝ r (fun y ↦ seedEigenvalue n*(u y*u y)) x‖ ≤
      10*((2:ℝ)^r*A*A)*(n:ℝ)^(r+8)*H^2 := by
    change ‖iteratedFDeriv ℝ r (seedEigenvalue n • (fun y ↦ u y*u y)) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply ((hu.mul hu).of_le
      (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg hlam]
    calc
      _ ≤ (10*(n:ℝ)^2)*((2:ℝ)^r*A*A*(n:ℝ)^(r+3+3)*(H*H)) := by gcongr
      _ = _ := by
        rw [show r+8 = 2+(r+3+3) by omega,pow_add]
        ring
  rw [roundDenominator_sum,fun_iteratedFDeriv_add_apply
    ((ContDiff.sum (fun i _ ↦ roundCoordFactor_smooth.mul ((hp i).mul (hp i)))).of_le
      (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    ((contDiff_const.mul (hu.mul hu)).of_le
      (by exact_mod_cast (show (r:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  have h := (norm_add_le _ _).trans (add_le_add hsum heigen)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | dsimp [C]; ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedDivergenceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma scaled_frequency_product (f g : Yau.Jets.Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Yau.Jets.Coord)
    (r s a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(s*i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(s*i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(s*r+a+b)*(H*K) :=
  scaled_frequency_product_on f g isOpen_univ hf.contDiffOn hg.contDiffOn x (mem_univ x)
    r s a b hN hA hB hH hK hfb hgb

theorem weighted_divergence_frequency_bound (gamma : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ (V : Yau.Jets.Coord → Yau.Jets.Coord),
      (∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) → ∀ (N B : ℝ), 1 ≤ N → 0 ≤ B →
      ∀ (a : ℕ) (x : Yau.Jets.Coord), x ∈ Q →
      (∀ i j, j ≤ r+1 → ‖iteratedFDeriv ℝ j (fun y ↦ V y i) x‖ ≤ B*N^(137*j+a)) →
      ‖iteratedFDeriv ℝ r (Yau.weightedDiv gamma V) x‖ ≤ C*B*N^(137*r+a+137) := by
  obtain ⟨G,hG,hgb⟩ := compact_real_derivative_bound gamma hg hQ (r+1)
  obtain ⟨I,hI,hib⟩ := compact_real_derivative_bound (fun x ↦ (gamma x)⁻¹) (hg.inv hgn) hQ r
  refine ⟨(2:ℝ)^r*I*(4*((2:ℝ)^(r+1)*G)),by positivity,?_⟩
  intro V hV N B hN hB a x hx hv
  have hN0 : 0 ≤ N := by linarith
  let W : Fin 4 → Yau.Jets.Coord → ℝ := fun i y ↦ gamma y*V y i
  have hW (i : Fin 4) : ContDiff ℝ ∞ (W i) := hg.mul (hV i)
  have hw (i : Fin 4) (j : ℕ) (hj : j ≤ r+1) :
      ‖iteratedFDeriv ℝ j (W i) x‖ ≤ ((2:ℝ)^(r+1)*G*B)*N^(137*j+a) := by
    have h := scaled_frequency_product gamma (fun y ↦ V y i) hg (hV i) x j 137 0 a
      hN0 hG.le hB (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
      (fun k hk ↦ (hgb k (by omega) x hx).trans (by
        have hp : 1 ≤ N^(137*k+0) := one_le_pow₀ hN
        simpa using le_mul_of_one_le_right hG.le hp))
      (fun k hk ↦ by simpa using hv i k (by omega))
    simp only [Nat.add_zero,mul_one] at h
    exact h.trans (by gcongr; norm_num)
  let div : Yau.Jets.Coord → ℝ := fun y ↦ ∑ i : Fin 4, fderiv ℝ (W i) y (Pi.single i 1)
  have hpartial (i : Fin 4) : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ (W i) y (Pi.single i 1)) :=
    ((hW i).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hdiv : ContDiff ℝ ∞ div := ContDiff.sum (fun i _ ↦ hpartial i)
  have hdb (j : ℕ) (hj : j ≤ r) :
      ‖iteratedFDeriv ℝ j div x‖ ≤ (4*((2:ℝ)^(r+1)*G*B))*N^(137*j+(a+137)) := by
    have hb (i : Fin 4) := (real_partial_iterated_bound (W i) (hW i) x i j).trans
      (hw i (j+1) (by omega))
    dsimp [div]
    rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
      ((hpartial i).of_le
        (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
    have h := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun i _ ↦ hb i))
    simpa [show 137*(j+1)+a = 137*j+(a+137) by omega,mul_assoc] using h
  have h := scaled_frequency_product (fun y ↦ (gamma y)⁻¹) div (hg.inv hgn) hdiv x r 137 0 (a+137) (B := 4*((2:ℝ)^(r+1)*G*B))
    hN0 hI.le (by positivity) (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun j hj ↦ (hib j hj x hx).trans (by
      have hp : 1 ≤ N^(137*j+0) := one_le_pow₀ hN
      simpa using le_mul_of_one_le_right hI.le hp))
    (fun j hj ↦ by simpa using hdb j hj)
  convert h using 1 <;> first | rfl | simp only [Nat.add_zero,mul_one,Nat.add_assoc]; ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CorrectionProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma correction_product_bound (f v : Yau.Jets.Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (x : Yau.Jets.Coord)
    (r b : ℕ) {N A B H : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 < H)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(137*i+128)*H⁻¹)
    (hvb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i v x‖ ≤ B*N^(i+b)*H) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*v y) x‖ ≤ (2:ℝ)^r*A*B*N^(137*r+128+b) := by
  have h := scaled_frequency_product f v hf hv x r 137 128 b (by linarith) hA hB
    (by positivity) hH.le hfb (fun i hi ↦ (hvb i hi).trans (by gcongr; omega))
  simpa [inv_mul_cancel₀ hH.ne'] using h

theorem compact_multiplier_frequency_bound (q : Yau.Jets.Coord → ℝ) (hq : ContDiff ℝ ∞ q)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ (v : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ v →
      ∀ (N B : ℝ), 1 ≤ N → 0 ≤ B → ∀ (a : ℕ) (x : Yau.Jets.Coord), x ∈ Q →
      (∀ i, i ≤ r → ‖iteratedFDeriv ℝ i v x‖ ≤ B*N^(137*i+a)) →
      ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i (fun y ↦ q y*v y) x‖ ≤ C*B*N^(137*i+a) := by
  obtain ⟨G,hG,hgb⟩ := compact_real_derivative_bound q hq hQ r
  refine ⟨(2:ℝ)^r*G,by positivity,?_⟩
  intro v hv N B hN hB a x hx hb i hi
  have h := scaled_frequency_product q v hq hv x i 137 0 a (N := N) (by linarith) hG.le hB
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun j hj ↦ (hgb j (by omega) x hx).trans (by
      have hp : 1 ≤ N^(137*j+0) := one_le_pow₀ hN
      simpa using le_mul_of_one_le_right hG.le hp))
    (fun j hj ↦ by simpa using hb j (by omega))
  simp only [Nat.add_zero,mul_one] at h
  exact h.trans (by gcongr; norm_num)

theorem weighted_divergence_finite_frequency_bound (gamma : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ (V : Yau.Jets.Coord → Yau.Jets.Coord),
      (∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) → ∀ (N B : ℝ), 1 ≤ N → 0 ≤ B →
      ∀ (a : ℕ) (x : Yau.Jets.Coord), x ∈ Q →
      (∀ i j, j ≤ r+1 → ‖iteratedFDeriv ℝ j (fun y ↦ V y i) x‖ ≤ B*N^(137*j+a)) →
      ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i (Yau.weightedDiv gamma V) x‖ ≤ C*B*N^(137*i+a+137) := by
  have hb (i : Fin (r+1)) := weighted_divergence_frequency_bound gamma hg hgn hQ i.val
  choose c hc hbound using hb
  let C : ℝ := 1+∑ i, c i
  have hc0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ (hc i).le)
  refine ⟨C,by dsimp [C] <;> linarith,?_⟩
  intro V hV N B hN hB a x hx hb i hi
  have h := hbound ⟨i,by omega⟩ V hV N B hN hB a x hx (fun l j hj ↦ hb l j (by omega))
  have hsum := Finset.single_le_sum (fun j _ ↦ (hc j).le)
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (r+1)))
  have hci : c ⟨i,by omega⟩ ≤ C := by dsimp [C] <;> linarith
  exact h.trans (by gcongr)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCorrectionResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

lemma seedCoordDensity_smooth (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) : ContDiff ℝ ∞ (seedCoordDensity rho) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (smooth_inverse_chart_comp rho hr seedPoint
    (by rw [centeredSphereChart_target]; trivial)).comp x seedCoordEquiv.contDiff.contDiffAt

theorem intrinsicCorrectionResidual_bound (A : IntrinsicTensor) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ B > 0, ∀ (lam : ℝ) (u : _root_.OAI.Yau.Jets.Coord → ℝ),
      let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) lam u
      ContDiff ℝ ∞ R → tsupport R ⊆ Q →
      ContDiff ℝ ∞ (intrinsicCorrectionResidual A rho lam u) ∧
      tsupport (intrinsicCorrectionResidual A rho lam u) ⊆ Q ∧
      ∀ (H : _root_.OAI.Yau.Jets.Coord → ℝ), (∀ x, 0 ≤ H x) →
        (∀ x, DerivativeBound k R x (H x)) → ∀ x,
          DerivativeBound k (intrinsicCorrectionResidual A rho lam u) x (B*H x) := by
  have hmul := compact_residual_multiplier (fun x ↦ -(seedCoordDensity rho x:ℂ))
    (Complex.ofRealCLM.contDiff.comp (seedCoordDensity_smooth rho hr)).neg hQ k
  obtain ⟨B,hB,h⟩ := hmul
  exact ⟨B,hB,fun lam u ↦ h _⟩

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RoundSupportedCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem round_supported_exact_correction (u R H : Yau.Jets.Coord → ℝ)
    {Ω Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hu : ContDiff ℝ ∞ u) (hR : ContDiff ℝ ∞ R) (hsupport : tsupport R ⊆ Q)
    {n : ℕ} (hn : 0 < n) (hH : ∀ x ∈ Ω, 0 < H x)
    (hjet : ∀ x ∈ Ω, ((n:ℝ)^65)⁻¹*H x ≤ sourceFirstJetSize u n x) :
    ∃ f : Yau.Jets.Coord → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ tsupport R ∧
      (∀ x, f x = R x / roundCorrectionDenominator u n x) ∧
      ∀ x, Yau.weightedDiv roundCoordDensity
          (fun y i ↦ u y * (f y * roundCoordGradient u y i)) x +
        seedEigenvalue n * (f x * u x - (seedEigenvalue n)⁻¹ *
          Yau.weightedDiv roundCoordDensity (fun y i ↦ f y * roundCoordGradient u y i) x) * u x = R x := by
  have hden : ∀ x ∈ tsupport R,
      Yau.correctionDenominator u (roundCoordGradient u) (seedEigenvalue n) x ≠ 0 := by
    intro x hx
    exact ne_of_gt (roundCorrectionDenominator_pos u hn x (hH x (hQΩ (hsupport hx)))
      (hjet x (hQΩ (hsupport hx))))
  have hlam : seedEigenvalue n ≠ 0 := by
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    unfold seedEigenvalue
    positivity
  exact Yau.global_exact_correction roundCoordDensity_smooth
    (fun x ↦ ne_of_gt (roundCoordDensity_pos x)) hu hR
    (hQ.of_isClosed_subset isClosed_closure hsupport)
    (fun i ↦ (contDiff_pi.mp (roundCoordGradient_smooth u hu)) i) hlam hden

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicRealCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

lemma intrinsicRealCorrectionResidual_support (A : IntrinsicTensor) (rho : Base → ℝ)
    (lam : ℝ) (u : Yau.Jets.Coord → ℝ) :
    tsupport (intrinsicRealCorrectionResidual A rho lam u) ⊆
      tsupport (intrinsicCorrectionResidual A rho lam u) := by
  apply closure_mono
  intro x hx hz
  apply hx
  simp only [intrinsicRealCorrectionResidual,hz,Complex.zero_re]

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ReciprocalFrequencyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem reciprocal_frequency_bound (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (f : E → ℝ), ContDiff ℝ ∞ f → ∀ (x : E) (N H : ℝ),
      1 ≤ N → 0 < H →
      (1/2:ℝ)*(N^128)⁻¹*H^2 ≤ f x →
      (∀ i, 1 ≤ i → i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(i+8)*H^2) →
      ‖iteratedFDeriv ℝ r (fun y ↦ (f y)⁻¹) x‖ ≤ C*N^(137*r+128)*(H^2)⁻¹ := by
  obtain ⟨C,hC,hb⟩ := reciprocal_derivative_bound (E := E) r
  let B : ℝ := max 1 (2*A)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBA : 2*A ≤ B := le_max_right _ _
  refine ⟨2*C*B^r,by positivity,?_⟩
  intro f hf x N H hN hH hl hu
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hf0 : 0 < f x := lt_of_lt_of_le (by positivity) hl
  have hratio (i : ℕ) (hi : 1 ≤ i) (hir : i ≤ r) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ |f x| * (B*N^137)^i := by
    rw [abs_of_pos hf0]
    have hpow : N^(i+136) ≤ N^(137*i) := by gcongr; omega
    have hBi : 2*A ≤ B^i := hBA.trans (le_self_pow₀ hB1 (by omega))
    calc
      _ ≤ A*N^(i+8)*H^2 := hu i hi hir
      _ = ((1/2:ℝ)*(N^128)⁻¹*H^2)*(2*A*N^(i+136)) := by
        rw [show i+136 = (i+8)+128 by omega,pow_add]
        field_simp
        ring
      _ ≤ f x * (2*A*N^(i+136)) := mul_le_mul_of_nonneg_right hl (by positivity)
      _ ≤ f x * (B^i*N^(137*i)) := by gcongr
      _ = f x * (B*N^137)^i := by rw [mul_pow,← pow_mul]
  have hinv : |f x|⁻¹ ≤ 2*N^128*(H^2)⁻¹ := by
    rw [abs_of_pos hf0]
    calc
      (f x)⁻¹ ≤ ((1/2:ℝ)*(N^128)⁻¹*H^2)⁻¹ := (inv_le_inv₀ hf0 (by positivity)).mpr hl
      _ = _ := by field_simp
  have h := hb f hf x hf0.ne' (B*N^137) (by positivity) hratio
  refine h.trans ?_
  calc
    C*|f x|⁻¹*(B*N^137)^r ≤ C*(2*N^128*(H^2)⁻¹)*(B*N^137)^r := by gcongr
    _ = _ := by rw [mul_pow,← pow_mul,pow_add]; ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RoundReciprocalDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

theorem round_denominator_finite_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ∀ (n : ℕ), 0 < n →
      ∀ (x : Yau.Jets.Coord), x ∈ Q → ∀ (H : ℝ), 0 < H →
      (∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H) →
      ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i (roundCorrectionDenominator u n) x‖ ≤
        C*(n:ℝ)^(i+8)*H^2 := by
  have hb (i : Fin (r+1)) := round_denominator_derivative_bound hQ i.val hA
  choose c hc hbound using hb
  let C : ℝ := 1+∑ i, c i
  have hc0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ (hc i).le)
  refine ⟨C,by dsimp [C] <;> linarith,?_⟩
  intro u hu n hn x hx H hH hub i hi
  have hb := hbound ⟨i,by omega⟩ u hu n hn x hx H hH (fun j hj ↦ hub j (by omega))
  have hsum := Finset.single_le_sum (fun j _ ↦ (hc j).le)
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (r+1)))
  have hci : c ⟨i,by omega⟩ ≤ C := by dsimp [C] <;> linarith
  exact hb.trans (by gcongr)

theorem round_reciprocal_derivative_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ∀ (n : ℕ), 0 < n →
      ∀ (x : Yau.Jets.Coord), x ∈ Q → ∀ (H : ℝ), 0 < H →
      (∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H) →
      ((n:ℝ)^65)⁻¹*H ≤ sourceFirstJetSize u n x →
      ‖iteratedFDeriv ℝ r (fun y ↦ (roundCorrectionDenominator u n y)⁻¹) x‖ ≤
        C*(n:ℝ)^(137*r+128)*(H^2)⁻¹ := by
  obtain ⟨B,hB,hden⟩ := round_denominator_finite_bound hQ r hA
  obtain ⟨C,hC,hrec⟩ := reciprocal_frequency_bound (E := Yau.Jets.Coord) r hB
  refine ⟨C,hC,?_⟩
  intro u hu n hn x hx H hH hub hjet
  exact hrec _ (roundCorrectionDenominator_smooth u hu n) x n H
    (by exact_mod_cast hn) hH (roundCorrectionDenominator_lower u hn x hH hjet)
    (fun i _ hi ↦ hden u hu n hn x hx H hH hub i hi)

theorem round_reciprocal_finite_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ∀ (n : ℕ), 0 < n →
      ∀ (x : Yau.Jets.Coord), x ∈ Q → ∀ (H : ℝ), 0 < H →
      (∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H) →
      ((n:ℝ)^65)⁻¹*H ≤ sourceFirstJetSize u n x →
      ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i (fun y ↦ (roundCorrectionDenominator u n y)⁻¹) x‖ ≤
        C*(n:ℝ)^(137*i+128)*(H^2)⁻¹ := by
  have hb (i : Fin (r+1)) := round_reciprocal_derivative_bound hQ i.val hA
  choose c hc hbound using hb
  let C : ℝ := 1+∑ i, c i
  have hc0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ (hc i).le)
  refine ⟨C,by dsimp [C] <;> linarith,?_⟩
  intro u hu n hn x hx H hH hub hjet i hi
  have hb := hbound ⟨i,by omega⟩ u hu n hn x hx H hH
    (fun j hj ↦ hub j (by omega)) hjet
  have hsum := Finset.single_le_sum (fun j _ ↦ (hc j).le)
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (r+1)))
  have hci : c ⟨i,by omega⟩ ≤ C := by dsimp [C] <;> linarith
  exact hb.trans (by gcongr)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RoundQuotientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem round_quotient_finite_bound {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u R H : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ContDiff ℝ ∞ R →
      tsupport R ⊆ Q → (∀ x, 0 < H x) → ∀ (n : ℕ), 0 < n → ∀ eps : ℝ, 0 < eps →
      (∀ x ∈ Q, ∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H x) →
      (∀ x ∈ Q, ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i R x‖ ≤ eps*H x) →
      (∀ x ∈ Q, ((n:ℝ)^65)⁻¹*H x ≤ sourceFirstJetSize u n x) →
      let f := fun x ↦ R x / roundCorrectionDenominator u n x
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ tsupport R ∧
      ∀ x, ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤
        C*eps*(n:ℝ)^(137*i+128)*(H x)⁻¹ := by
  obtain ⟨B,hB,hrec⟩ := round_reciprocal_finite_bound hQ r hA
  refine ⟨(2:ℝ)^r*B,by positivity,?_⟩
  intro u R H hu hR hs hH n hn eps heps hub hRb hjet
  let D := roundCorrectionDenominator u n
  have hD : ContDiff ℝ ∞ D := roundCorrectionDenominator_smooth u hu n
  have hDQ (x : Yau.Jets.Coord) (hx : x ∈ Q) : D x ≠ 0 :=
    (roundCorrectionDenominator_pos u hn x (hH x) (hjet x hx)).ne'
  have hf := Yau.smooth_quotient_on_residual_support hR hD (fun x hx ↦ hDQ x (hs hx))
  refine ⟨hf,Yau.quotient_compact_support (hQ.of_isClosed_subset isClosed_closure hs),
    Yau.quotient_tsupport_subset R D,?_⟩
  intro x i hi
  have hHx := hH x
  by_cases hx : x ∈ Q
  · let U : Set Yau.Jets.Coord := {y | D y ≠ 0}
    have hU : IsOpen U := isOpen_ne_fun hD.continuous continuous_const
    have hxU : x ∈ U := hDQ x hx
    have hiD : ContDiffOn ℝ ∞ (fun y ↦ (D y)⁻¹) U :=
      hD.contDiffOn.inv (fun y hy ↦ hy)
    have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hbR (j : ℕ) (hj : j ≤ i) :
        ‖iteratedFDeriv ℝ j R x‖ ≤ eps*(n:ℝ)^(137*j+0)*H x := by
      exact (hRb x hx j (by omega)).trans (by
        have hp : 1 ≤ (n:ℝ)^(137*j+0) := one_le_pow₀ hN
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) (mul_nonneg heps.le (hH x).le)])
    have hbI (j : ℕ) (hj : j ≤ i) :
        ‖iteratedFDeriv ℝ j (fun y ↦ (D y)⁻¹) x‖ ≤
          B*(n:ℝ)^(137*j+128)*((H x)^2)⁻¹ :=
      hrec u hu n hn x hx (H x) (hH x) (hub x hx) (hjet x hx) j (by omega)
    have h := scaled_frequency_product_on R (fun y ↦ (D y)⁻¹) hU hR.contDiffOn hiD
      x hxU i 137 0 128 (by positivity) heps.le hB.le (hH x).le (by positivity) hbR hbI
    have he : H x*((H x)^2)⁻¹ = (H x)⁻¹ := by field_simp [(hH x).ne']
    simp only [Nat.add_zero,he] at h
    change ‖iteratedFDeriv ℝ i (fun y ↦ R y / D y) x‖ ≤ _
    simp only [div_eq_mul_inv]
    refine h.trans ?_
    calc
      _ ≤ (2:ℝ)^r*eps*B*(n:ℝ)^(137*i+128)*(H x)⁻¹ := by gcongr; norm_num
      _ = _ := by ring
  · have hxs : x ∉ tsupport (fun y ↦ R y / D y) :=
      fun h ↦ hx (hs (Yau.quotient_tsupport_subset R D h))
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hxs).iteratedFDeriv ℝ i
    rw [hz.eq_of_nhds]
    simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
    positivity

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RoundCorrectionSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem round_correction_size {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u R H : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ContDiff ℝ ∞ R →
      tsupport R ⊆ Q → (∀ x, 0 < H x) → ∀ (n : ℕ), 0 < n → ∀ eps : ℝ, 0 < eps →
      (∀ x ∈ Q, ∀ i, i ≤ r+2 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H x) →
      (∀ x ∈ Q, ∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i R x‖ ≤ eps*H x) →
      (∀ x ∈ Q, ((n:ℝ)^65)⁻¹*H x ≤ sourceFirstJetSize u n x) →
      let f := fun x ↦ R x / roundCorrectionDenominator u n x
      let alpha := fun x ↦ f x*u x
      let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
      tsupport alpha ⊆ tsupport R ∧ tsupport beta ⊆ tsupport R ∧
      ∀ x i, i ≤ r → ‖iteratedFDeriv ℝ i alpha x‖ + ‖iteratedFDeriv ℝ i beta x‖ ≤
        C*eps*(n:ℝ)^(137*r+267) := by
  obtain ⟨F,hF,hquot⟩ := round_quotient_finite_bound hQ (r+1) hA
  obtain ⟨G,hG,hmul⟩ := compact_multiplier_frequency_bound roundCoordFactor roundCoordFactor_smooth hQ (r+1)
  obtain ⟨D,hD,hdiv⟩ := weighted_divergence_finite_frequency_bound roundCoordDensity
    roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne') hQ r
  let L : ℝ := (2:ℝ)^(r+1)*F*A
  refine ⟨2*L+D*G*L,by dsimp [L] <;> positivity,?_⟩
  intro u R H hu hR hs hH n hn eps heps hub hRb hjet
  let f := fun x ↦ R x / roundCorrectionDenominator u n x
  obtain ⟨hf,hfc,hfs,hfb⟩ := hquot u R H hu hR hs hH n hn eps heps
    (fun x hx i hi ↦ hub x hx i (by omega)) hRb hjet
  let alpha := fun x ↦ f x*u x
  let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
  have ha : ContDiff ℝ ∞ alpha := hf.mul hu
  have hbeta : ContDiff ℝ ∞ beta := Yau.densityCorrection_smooth roundCoordDensity_smooth
    (fun x ↦ (roundCoordDensity_pos x).ne') hu hf
    (fun i ↦ contDiff_pi.mp (roundCoordGradient_smooth u hu) i) _
  have has : tsupport alpha ⊆ tsupport R := by
    apply (show tsupport alpha ⊆ tsupport f from ?_).trans hfs
    apply closure_mono
    intro x hx
    exact fun h ↦ hx (by simp [alpha,h])
  have hbs : tsupport beta ⊆ tsupport R :=
    (Yau.densityCorrection_tsupport_subset _ _ _ _ _).trans hfs
  refine ⟨hf,ha,hbeta,has,hbs,?_⟩
  intro x i hi
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0:ℝ) < n := by exact_mod_cast hn
  have hHx := hH x
  have hL : 0 < L := by dsimp [L] <;> positivity
  by_cases hx : x ∈ Q
  · have hp (j : Fin 4) : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ u y (Pi.single j 1)) :=
      (hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
    have haBound (j : ℕ) (hj : j ≤ r+1) :
        ‖iteratedFDeriv ℝ j alpha x‖ ≤ L*eps*(n:ℝ)^(137*j+131) := by
      have h := correction_product_bound f u hf hu x j 3 hN (mul_nonneg hF.le heps.le) hA.le hHx
        (fun k hk ↦ hfb x k (by omega)) (fun k hk ↦ hub x hx k (by omega))
      calc
        _ ≤ (2:ℝ)^(r+1)*(F*eps)*A*(n:ℝ)^(137*j+128+3) := by
          exact h.trans (by gcongr; norm_num)
        _ = _ := by dsimp [L]; congr 1; ring
    have hpBound (l : Fin 4) (j : ℕ) (hj : j ≤ r+1) :
        ‖iteratedFDeriv ℝ j (fun y ↦ f y*fderiv ℝ u y (Pi.single l 1)) x‖ ≤
          L*eps*(n:ℝ)^(137*j+132) := by
      have hvb (k : ℕ) (hk : k ≤ j) :
          ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ u y (Pi.single l 1)) x‖ ≤
            A*(n:ℝ)^(k+4)*H x :=
        (real_partial_iterated_bound u hu x l k).trans (by
          simpa [Nat.add_assoc] using hub x hx (k+1) (by omega))
      have h := correction_product_bound f _ hf (hp l) x j 4 hN
        (mul_nonneg hF.le heps.le) hA.le hHx (fun k hk ↦ hfb x k (by omega)) hvb
      calc
        _ ≤ (2:ℝ)^(r+1)*(F*eps)*A*(n:ℝ)^(137*j+128+4) := by
          exact h.trans (by gcongr; norm_num)
        _ = _ := by dsimp [L]; congr 1; ring
    let V := fun y l ↦ f y*roundCoordGradient u y l
    have hV (l : Fin 4) : ContDiff ℝ ∞ (fun y ↦ V y l) :=
      hf.mul (contDiff_pi.mp (roundCoordGradient_smooth u hu) l)
    have hvb (l : Fin 4) (j : ℕ) (hj : j ≤ r+1) :
        ‖iteratedFDeriv ℝ j (fun y ↦ V y l) x‖ ≤ (G*L*eps)*(n:ℝ)^(137*j+132) := by
      have he : (fun y ↦ V y l) = fun y ↦ roundCoordFactor y*(f y*fderiv ℝ u y (Pi.single l 1)) := by
        funext y; dsimp [V,roundCoordGradient] <;> ring
      rw [he]
      have h := hmul _ (hf.mul (hp l)) n (L*eps) hN (by positivity) 132 x hx (hpBound l) j hj
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | ring
    have hd := hdiv V hV n (G*L*eps) hN (by positivity) 132 x hx hvb i hi
    have hlam : (n:ℝ)^2 ≤ seedEigenvalue n := by unfold seedEigenvalue; nlinarith
    have hlam0 : 0 < seedEigenvalue n := lt_of_lt_of_le (by positivity) hlam
    have hlaminv : (seedEigenvalue n)⁻¹ ≤ ((n:ℝ)^2)⁻¹ :=
      (inv_le_inv₀ hlam0 (by positivity)).mpr hlam
    have hds : ContDiff ℝ ∞ (Yau.weightedDiv roundCoordDensity V) :=
      Yau.weightedDiv_smooth roundCoordDensity_smooth (fun y ↦ (roundCoordDensity_pos y).ne') hV
    have hterm : ‖iteratedFDeriv ℝ i (fun y ↦ (seedEigenvalue n)⁻¹*Yau.weightedDiv roundCoordDensity V y) x‖ ≤
        (D*G*L)*eps*(n:ℝ)^(137*i+267) := by
      change ‖iteratedFDeriv ℝ i ((seedEigenvalue n)⁻¹ • Yau.weightedDiv roundCoordDensity V) x‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply (hds.of_le
        (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
        norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlam0)]
      calc
        _ ≤ ((n:ℝ)^2)⁻¹*(D*(G*L*eps)*(n:ℝ)^(137*i+132+137)) := by gcongr
        _ = _ := by
          rw [show 137*i+132+137 = 2+(137*i+267) by omega,pow_add]
          field_simp
    have hb : ‖iteratedFDeriv ℝ i beta x‖ ≤ (L+D*G*L)*eps*(n:ℝ)^(137*r+267) := by
      change ‖iteratedFDeriv ℝ i (fun y ↦ alpha y - (seedEigenvalue n)⁻¹*Yau.weightedDiv roundCoordDensity V y) x‖ ≤ _
      rw [fun_iteratedFDeriv_sub_apply (ha.of_le
        (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
        ((contDiff_const.mul hds).of_le
          (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
      have h := (norm_sub_le _ _).trans (add_le_add (haBound i (by omega)) hterm)
      refine h.trans ?_
      calc
        _ ≤ L*eps*(n:ℝ)^(137*r+267)+(D*G*L)*eps*(n:ℝ)^(137*r+267) := by gcongr; omega
        _ = _ := by ring
    have hab : ‖iteratedFDeriv ℝ i alpha x‖ ≤ L*eps*(n:ℝ)^(137*r+267) :=
      (haBound i (by omega)).trans (by gcongr; omega)
    have h := add_le_add hab hb
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | ring
  · have hax : x ∉ tsupport alpha := fun h ↦ hx (hs (has h))
    have hbx : x ∉ tsupport beta := fun h ↦ hx (hs (hbs h))
    rw [((notMem_tsupport_iff_eventuallyEq.mp hax).iteratedFDeriv ℝ i).eq_of_nhds,
      ((notMem_tsupport_iff_eventuallyEq.mp hbx).iteratedFDeriv ℝ i).eq_of_nhds]
    simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero,zero_add]
    positivity

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_IntrinsicCorrectionSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem intrinsic_real_correction_size (A : IntrinsicTensor) (rho : Base → ℝ)
    (hrs : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ C > 0, ∀ (u H : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u →
      (∀ x, 0 < H x) → ∀ (n : ℕ), 0 < n → ∀ eps : ℝ, 0 < eps →
      let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n) u
      ContDiff ℝ ∞ R → tsupport R ⊆ Q →
      (∀ x, DerivativeBound (r+1) R x (eps*H x)) →
      (∀ x ∈ Q, ∀ i, i ≤ r+2 → ‖iteratedFDeriv ℝ i u x‖ ≤ B*(n:ℝ)^(i+3)*H x) →
      (∀ x ∈ Q, ((n:ℝ)^65)⁻¹*H x ≤ sourceFirstJetSize u n x) →
      let R0 := intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u
      let f := fun x ↦ R0 x / roundCorrectionDenominator u n x
      let alpha := fun x ↦ f x*u x
      let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
      tsupport alpha ⊆ Q ∧ tsupport beta ⊆ Q ∧
      (∀ x i, i ≤ r → ‖iteratedFDeriv ℝ i alpha x‖ + ‖iteratedFDeriv ℝ i beta x‖ ≤
        C*eps*(n:ℝ)^(137*r+267)) ∧
      ∀ x, Yau.weightedDiv roundCoordDensity
        (fun y i ↦ alpha y * roundCoordGradient u y i) x + seedEigenvalue n*beta x*u x = R0 x := by
  obtain ⟨M,hM,hm⟩ := intrinsicCorrectionResidual_bound A rho hrs hQ (r+1)
  obtain ⟨C,hC,hsize⟩ := round_correction_size hQ r hB
  refine ⟨C*M,by positivity,?_⟩
  intro u H hu hH n hn eps heps R hR hsup hRb hub hjet
  obtain ⟨hsm,hs,hbound⟩ := hm (seedEigenvalue n) u hR hsup
  let R0 := intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u
  have hR0 : ContDiff ℝ ∞ R0 := Complex.reCLM.contDiff.comp hsm
  have hs0 : tsupport R0 ⊆ Q := (intrinsicRealCorrectionResidual_support A rho _ u).trans hs
  have hR0b (x : Yau.Jets.Coord) (i : ℕ) (hi : i ≤ r+1) :
      ‖iteratedFDeriv ℝ i R0 x‖ ≤ (M*eps)*H x := by
    have h := Complex.reCLM.norm_iteratedFDeriv_comp_left hsm.contDiffAt
      (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top)) (x := x)
    rw [Complex.reCLM_norm,one_mul] at h
    have hb := hbound (fun y ↦ eps*H y) (fun y ↦ mul_nonneg heps.le (hH y).le) hRb x i hi
    exact h.trans (by simpa [mul_assoc] using hb)
  obtain ⟨hf,ha,hbeta,has,hbs,hb⟩ := hsize u R0 H hu hR0 hs0 hH n hn (M*eps)
    (by positivity) hub (fun x _ i hi ↦ hR0b x i hi) hjet
  refine ⟨hf,ha,hbeta,has.trans hs0,hbs.trans hs0,?_,?_⟩
  · intro x i hi
    simpa [mul_assoc] using hb x i hi
  · obtain ⟨f,hf',hfc,hfs,hval,heq⟩ := round_supported_exact_correction u R0 H hQ
      (Subset.refl Q) hu hR0 hs0 hn (fun x _ ↦ hH x) hjet
    have he : f = fun x ↦ R0 x / roundCorrectionDenominator u n x := funext hval
    subst f
    intro x
    convert heq x using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    congr 1
    funext y i
    ring

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

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LiteralSeededFieldBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem literal_seeded_lattice_field_bound (hUD : U ⊆ D) (hUb : Bornology.IsBounded U)
    {Q : Set _root_.OAI.Yau.Jets.Coord} (hQ : IsCompact Q) (hQB : Q ⊆ seedCoordBranch) :
    ∃ C > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n),
      letI := hfin
      ∀ coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ,
        coeff ∈ coefficientEvent (n:ℝ) →
        let u := fun z ↦ seedCoordinateField n z + gaussianWaveField
          (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff z
        ContDiff ℝ ∞ u ∧ ∀ x ∈ Q, ∀ k : Fin (k0+1),
          ‖iteratedFDeriv ℝ k.val u x‖ ≤ C*(n:ℝ)^(k.val+3)*
            max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*seedCoordReal x)) := by
  have hs (j : Fin (k0+1)) := seedCoordinateField_derivative_bound hQ hQB j.val
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
  have hseedSmooth := seedCoordinateField_smooth n
  refine ⟨hseedSmooth.add hV,?_⟩
  intro x hx k
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
  have hseed' : ‖iteratedFDeriv ℝ k.val (seedCoordinateField n) x‖ ≤
      B*(n:ℝ)^(k.val+3)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*seedCoordReal x)) := by
    have h := hseed k n hnpos x hx
    refine h.trans ?_
    have hbB : b k ≤ B := Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _)
    gcongr
    · omega
    · exact le_max_right _ _
  have hrand : ‖iteratedFDeriv ℝ k.val (gaussianWaveField
      (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) x‖ ≤
      C*(n:ℝ)^(k.val+3)*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*seedCoordReal x)) := by
    refine (hVb x k).trans ?_
    gcongr
    exact le_max_left _ _
  change ‖iteratedFDeriv ℝ k.val (seedCoordinateField n + gaussianWaveField
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2) coeff) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hseedSmooth.of_le
    (by exact_mod_cast (show (k.val:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hV.of_le (by exact_mod_cast (show (k.val:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  have h := (norm_add_le _ _).trans (add_le_add hseed' hrand)
  convert h using 1 <;> first | rfl | ring

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IntrinsicPackedSmallCorrectedStage
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

theorem intrinsic_packed_small_corrected_stage_oai :
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
      (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∀ (T : ℝ) (J0 : ℕ),
      let k0 := max 5 (J0+2)
      let K' := 137*J0+269
      ∃ d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T,
      ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set Yau.Jets.Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let u := fun x ↦ seedCoordinateField n x + gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff x
            let R0 := intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u
            let f := fun x ↦ R0 x / roundCorrectionDenominator u n x
            let alpha := fun x ↦ f x*u x
            let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
            coeff ∈ coefficientEvent (n:ℝ) ∧ ContDiff ℝ ∞ u ∧
            (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
              (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize u n x) ∧
            ENNReal.ofReal (c*((n:ℝ)*(∫ x in seedCoordCube a,
              sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
              Measure.hausdorffMeasure (4:ℝ)
                ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Yau.Jets.Coord × ℝ | u y.1 = 0}) ∧
            LiteralNodalCertificate (intrinsicSeedCoordMetric A rho) d.S (seedCoordCube a) d.U n u
              (c*((n:ℝ)*(∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ∧
            ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
            tsupport alpha ⊆ Q ∧ tsupport beta ⊆ Q ∧
            (∀ x i, i ≤ J0 → ‖iteratedFDeriv ℝ i alpha x‖ + ‖iteratedFDeriv ℝ i beta x‖ ≤
              C*((n:ℝ)^2)⁻¹) ∧
            ∀ x, Yau.weightedDiv roundCoordDensity
              (fun y i ↦ alpha y * roundCoordGradient u y i) x + seedEigenvalue n*beta x*u x = R0 x := by
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,hstage⟩ := intrinsic_packed_selected_stage
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  obtain ⟨c,hc,hstage⟩ := hstage A hAs hs hp rho hrs hrp hclose K hK hKP hA hrho
  refine ⟨c,hc,?_⟩
  intro T J0 k0 K'
  have hk0 : 5 ≤ k0 := le_max_left _ _
  have hJ : J0+2 ≤ k0 := le_max_right _ _
  obtain ⟨d,b,hb,C,hC,Q,hQ,hQΩ,hUQ,hKQ,hselect⟩ :=
    hstage T k0 K' hk0
  have hQB : Q ⊆ seedCoordBranch := hQΩ.trans (subset_closure.trans d.closure_Ω_branch)
  obtain ⟨F,hF,hfield⟩ := literal_seeded_lattice_field_bound b subset_closure (d.compact_closure_U.isBounded.subset subset_closure) hQ hQB
  obtain ⟨B,hB,hcorr⟩ := intrinsic_real_correction_size A rho hrs hQ J0 hF
  refine ⟨d,b,hb,B*C,by positivity,Q,hQ,hQΩ,hUQ,hKQ,?_⟩
  filter_upwards [hselect,hfield,eventually_gt_atTop (0:ℕ)] with n hn hnfield hn0
  obtain ⟨hfin,coeff,hcoeff,hu,hR,hadd,hsup,hzero,hRb,hjet,hmeasure,hpacking⟩ := hn
  obtain ⟨hfin',hfbound⟩ := hnfield
  have he : hfin' = hfin := Subsingleton.elim _ _
  subst hfin'
  let := hfin
  obtain ⟨_,hub⟩ := hfbound coeff hcoeff
  let u := fun x ↦ seedCoordinateField n x + gaussianWaveField
    (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff x
  let H := fun x ↦ max (Real.exp ((n:ℝ)*d.S x)) (Real.exp ((n:ℝ)*seedCoordReal x))
  have hH (x : Yau.Jets.Coord) : 0 < H x := (Real.exp_pos _).trans_le (le_max_left _ _)
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
  let eps : ℝ := C*(n:ℝ)^(-(K':ℝ))
  have heps : 0 < eps := mul_pos hC (Real.rpow_pos_of_pos hnpos _)
  have hres : ∀ x, DerivativeBound (J0+1)
      (realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n) u)
      x (eps*H x) := by
    intro x i hi
    exact (hRb x i (by omega)).trans (by
      change C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x) ≤ eps*H x
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) heps.le)
  have huf (x : Yau.Jets.Coord) (hx : x ∈ Q) (i : ℕ) (hi : i ≤ J0+2) :=
    hub x hx (⟨i,by omega⟩ : Fin (k0+1))
  obtain ⟨hf,halpha,hbeta,has,hbs,hsize,heq⟩ := hcorr u H hu hH n hn0 eps heps hR hsup hres huf
    (fun x hx ↦ hjet x (subset_closure (hQΩ hx)))
  refine ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,?_,heq⟩
  intro x i hi
  refine (hsize x i hi).trans_eq ?_
  dsimp [eps,K']
  rw [Real.rpow_neg hnpos.le,Real.rpow_natCast]
  have he : 137*J0+269 = (137*J0+267)+2 := by omega
  rw [he,pow_add]
  field_simp

end
end Yau.Target

end OAI
end

theorem solution : type_of% @OAI.Yau.Target.intrinsic_packed_small_corrected_stage_oai := @OAI.Yau.Target.intrinsic_packed_small_corrected_stage_oai
