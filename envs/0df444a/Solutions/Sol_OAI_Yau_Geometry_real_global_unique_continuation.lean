-- Prove2me | solution 1 for OAI.Yau.Geometry.real_global_unique_continuation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:29:16.143078+00:00
-- url     : https://prove2.me/submissions/f0311a05-8968-49e2-a9d4-c419997ae202

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
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
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Definitions.Def_OAIQ237Ny004

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

lemma coordPartial_add {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (i : Fin 4) : coordPartial i (fun x ↦ f x + u x) =
      fun x ↦ coordPartial i f x + coordPartial i u x := by
  funext x
  unfold coordPartial
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hu.differentiable (by simp) x)]
  rfl

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

lemma coordPartial_exp {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    coordPartial i (fun x ↦ Complex.exp (f x)) =
      fun x ↦ coordPartial i f x * Complex.exp (f x) := by
  funext x
  unfold coordPartial
  rw [((hf.differentiable (by simp) x).hasFDerivAt.cexp).fderiv]
  simp [smul_eq_mul, mul_comm]

lemma coordPartial_twice_mul {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (i j : Fin 4) : coordPartial i (coordPartial j (fun x ↦ f x * u x)) = fun x ↦
      coordPartial i (coordPartial j f) x * u x +
      coordPartial j f x * coordPartial i u x +
      coordPartial i f x * coordPartial j u x +
      f x * coordPartial i (coordPartial j u) x := by
  rw [coordPartial_mul hf hu j,
    coordPartial_add ((coordPartial_contDiff hf j).mul hu) (hf.mul (coordPartial_contDiff hu j)),
    coordPartial_mul (coordPartial_contDiff hf j) hu i,
    coordPartial_mul hf (coordPartial_contDiff hu j) i]
  ext x
  ring

theorem smoothSecondOrder_mul (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (x : Coord) :
    smoothSecondOrder g b (fun z ↦ f z * u z) x =
      f x * smoothSecondOrder g b u x + u x * smoothSecondOrder g b f x +
      ∑ i, ∑ j, g i j x *
        (coordPartial i f x * coordPartial j u x + coordPartial j f x * coordPartial i u x) := by
  simp only [smoothSecondOrder]
  simp_rw [coordPartial_twice_mul hf hu]
  simp only [coordPartial_mul hf hu,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [mul_left_comm, mul_comm]
  ring

lemma waveExp_contDiff {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi) (N : ℝ) :
    ContDiff ℝ ∞ (waveExp phi N) := (contDiff_const.mul hp).cexp

lemma coordPartial_waveExp {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi) (N : ℝ) (i : Fin 4) :
    coordPartial i (waveExp phi N) =
      fun x ↦ (N : ℂ) * coordPartial i phi x * waveExp phi N x := by
  unfold waveExp
  rw [coordPartial_exp (contDiff_const.mul hp), coordPartial_const_mul hp]

lemma coordPartial_twice_waveExp {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (N : ℝ) (i j : Fin 4) : coordPartial i (coordPartial j (waveExp phi N)) =
      fun x ↦ ((N : ℂ) * coordPartial i (coordPartial j phi) x +
        (N : ℂ) ^ 2 * coordPartial i phi x * coordPartial j phi x) * waveExp phi N x := by
  rw [coordPartial_waveExp hp N j,
    coordPartial_mul (contDiff_const.mul (coordPartial_contDiff hp j)) (waveExp_contDiff hp N) i,
    coordPartial_const_mul (coordPartial_contDiff hp j), coordPartial_waveExp hp N i]
  ext x
  ring

theorem smoothSecondOrder_waveExp (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (N : ℝ) (x : Coord) :
    smoothSecondOrder g b (waveExp phi N) x =
      ((N : ℂ) * smoothSecondOrder g b phi x +
        (N : ℂ) ^ 2 * (smoothEikonal g phi x - 4)) * waveExp phi N x := by
  simp only [smoothSecondOrder]
  simp_rw [coordPartial_twice_waveExp hp N]
  simp only [coordPartial_waveExp hp N, smoothEikonal, add_sub_cancel_right,
    mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm]
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

end
end Yau.Geometry

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

theorem weightedDiv_smooth {gamma : Coord n → ℝ} {V : Coord n → Coord n}
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    ContDiff ℝ ∞ (weightedDiv gamma V) := by
  apply (hg.inv hgn).mul
  apply ContDiff.sum
  intro i _
  exact (((hg.mul (hV i)).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactWeightedDivergenceIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open Set MeasureTheory
open scoped ContDiff
noncomputable section
variable {d : ℕ}

lemma integral_directional_derivative_compact_zero (g : Coord d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (v : Coord d) :
    (∫ x, fderiv ℝ g x v) = 0 := by
  have hd : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ g x v) :=
    (hg.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hi : Integrable (fun x ↦ fderiv ℝ g x v) := hd.continuous.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Coord d ↦ (1:ℝ)) (g := g) (v := v)
    (by simp) (by simpa using hi)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ ↦ differentiableAt_const 1) (fun x _ ↦ hg.differentiable (by simp) x)
  simpa using h

theorem integral_weightedDiv_compact_zero (gamma : Coord d → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (V : Coord d → Coord d) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (hc : ∀ i, HasCompactSupport (fun x ↦ V x i)) :
    Integrable (fun x ↦ gamma x*weightedDiv gamma V x) ∧
    (∫ x, gamma x*weightedDiv gamma V x) = 0 := by
  let W : Fin d → Coord d → ℝ := fun i x ↦ gamma x*V x i
  have hW (i : Fin d) : ContDiff ℝ ∞ (W i) := hg.mul (hV i)
  have hWc (i : Fin d) : HasCompactSupport (W i) := (hc i).mul_left
  have hd (i : Fin d) : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ (W i) x (Pi.single i 1)) :=
    ((hW i).fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hi (i : Fin d) : Integrable (fun x ↦ fderiv ℝ (W i) x (Pi.single i 1)) :=
    (hd i).continuous.integrable_of_hasCompactSupport ((hWc i).fderiv_apply ℝ (Pi.single i 1))
  have he : (fun x ↦ gamma x*weightedDiv gamma V x) =
      (fun x ↦ ∑ i, fderiv ℝ (W i) x (Pi.single i 1)) := by
    funext x
    simp only [weightedDiv,coordDiv,coordPartial,← mul_assoc,mul_inv_cancel₀ (hgn x),one_mul,W]
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ ↦ hi i),?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp only [integral_directional_derivative_compact_zero _ (hW _) (hWc _),Finset.sum_const_zero]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCoordinateEllipticLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau
open scoped ContDiff
variable {n : ℕ}

lemma real_coordPartial_sum (f : Fin n → Coord n → ℝ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (x : Coord n) (i : Fin n) :
    coordPartial (fun y ↦ ∑ j, f j y) x i = ∑ j, coordPartial (f j) x i := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun j _ ↦ (hf j).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
  simp

theorem real_weighted_elliptic_expansion (gamma : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (B : Coord n → Fin n → Fin n → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (w : Coord n → ℝ) (hw : ContDiff ℝ ∞ w) (x : Coord n) :
    weightedDiv gamma (fun y i ↦ ∑ j, B y i j*coordPartial w y j) x =
      (∑ i, ∑ j, B x i j*coordPartial (fun y ↦ coordPartial w y j) x i) +
      ∑ j, realEllipticDrift gamma B x j*coordPartial w x j := by
  have he (i : Fin n) :
      (fun y ↦ gamma y*(∑ j, B y i j*coordPartial w y j)) =
      (fun y ↦ ∑ j, (gamma y*B y i j)*coordPartial w y j) := by
    funext y
    simp only [Finset.mul_sum,mul_assoc]
  unfold weightedDiv coordDiv
  simp_rw [he,real_coordPartial_sum _ (fun j ↦
    (hg.mul (hB _ j)).mul (real_coordPartial_smooth w hw j)),
    real_coordPartial_mul _ _ (hg.mul (hB _ _)) (real_coordPartial_smooth w hw _)]
  simp only [Finset.sum_add_distrib]
  have hcancel (i j : Fin n) :
      (gamma x)⁻¹ * ((gamma x*B x i j)*coordPartial (fun y ↦ coordPartial w y j) x i) =
      B x i j*coordPartial (fun y ↦ coordPartial w y j) x i := by
    rw [mul_assoc,← mul_assoc (gamma x)⁻¹,inv_mul_cancel₀ (hgn x),one_mul]
  simp only [mul_add,Finset.mul_sum,hcancel]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  unfold realEllipticDrift
  simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactWeightedWeakEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem compact_weighted_integration_by_parts (gamma phi : Coord n → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (V : Coord n → Coord n) (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    Integrable (fun x ↦ gamma x*pairing phi V x) ∧
    Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) ∧
    (∫ x, gamma x*pairing phi V x) = -(∫ x, gamma x*phi x*weightedDiv gamma V x) := by
  have hp : HasCompactSupport (pairing phi V) := by
    unfold pairing
    have h := HasCompactSupport.finset_sum
      (s := Finset.univ) (fun i _ ↦ (hc.fderiv_apply ℝ (Pi.single i 1)).mul_right
        (f' := fun x ↦ V x i))
    convert h using 1 <;> first | rfl | (ext x; simp [coordPartial])
  have hiP : Integrable (fun x ↦ gamma x*pairing phi V x) :=
    (hg.mul (pairing_smooth hphi hV)).continuous.integrable_of_hasCompactSupport hp.mul_left
  have hiD : Integrable (fun x ↦ gamma x*phi x*weightedDiv gamma V x) :=
    ((hg.mul hphi).mul (weightedDiv_smooth hg hgn hV)).continuous.integrable_of_hasCompactSupport
      hc.mul_left.mul_right
  obtain ⟨_,hz⟩ := integral_weightedDiv_compact_zero gamma hg hgn
    (fun x i ↦ phi x*V x i) (fun i ↦ hphi.mul (hV i)) (fun _ ↦ hc.mul_right)
  have he : (fun x ↦ gamma x*weightedDiv gamma (fun y i ↦ phi y*V y i) x) =
      (fun x ↦ gamma x*phi x*weightedDiv gamma V x + gamma x*pairing phi V x) := by
    funext x
    rw [weightedDiv_mul (hg.differentiable (by simp) x) (hgn x)
      (hphi.differentiable (by simp) x) (fun i ↦ (hV i).differentiable (by simp) x)]
    ring
  rw [he,integral_add hiD hiP] at hz
  exact ⟨hiP,hiD,by linarith⟩

end
end Yau

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinateMatrixEllipticity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma coordMatrixForm_apply (B : Matrix (Fin 4) (Fin 4) ℝ) (v w : _root_.OAI.Yau.Jets.Coord) :
    coordMatrixForm B v w = ∑ i, ∑ j, v i*B i j*w j := by
  simp [coordMatrixForm,mul_comm,mul_left_comm]

lemma coordMatrixForm_positive (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : B.PosDef)
    (v : _root_.OAI.Yau.Jets.Coord) (hv : v ≠ 0) : 0 < coordMatrixForm B v v := by
  rw [coordMatrixForm_apply]
  simpa [dotProduct,mulVec,Finset.mul_sum,mul_assoc] using hB.dotProduct_mulVec_pos hv

lemma coordMatrixForm_continuous {T : Type*} [TopologicalSpace T]
    (B : T → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, Continuous (fun x ↦ B x i j)) :
    Continuous (fun x ↦ coordMatrixForm (B x)) := by
  unfold coordMatrixForm
  exact continuous_finsetSum _ (fun i _ ↦ continuous_finsetSum _
    (fun j _ ↦ (hB i j).smul continuous_const))

lemma coord_norm_sq_le_sum_sq (v : _root_.OAI.Yau.Jets.Coord) : ‖v‖^2 ≤ ∑ i, v i^2 := by
  have h := norm_le_sourceEuclideanNorm v
  have he : sourceEuclideanNorm v ^ 2 = ∑ i, v i^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i)))
  nlinarith [norm_nonneg v,sourceEuclideanNorm_nonneg v]

lemma coord_sum_sq_le_four_norm_sq (v : _root_.OAI.Yau.Jets.Coord) : (∑ i, v i^2) ≤ 4*‖v‖^2 := by
  have h := sourceEuclideanNorm_le v
  have he : sourceEuclideanNorm v ^ 2 = ∑ i, v i^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i)))
  nlinarith [norm_nonneg v,sourceEuclideanNorm_nonneg v]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMatrixEnergy
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma realMatrixEnergy_apply (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B u v x = ∑ i, ∑ j, Yau.coordPartial u x i*B x i j*Yau.coordPartial v x j :=
  coordMatrixForm_apply _ _ _

lemma realMatrixEnergy_smooth (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (u v : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (realMatrixEnergy B u v) := by
  simp only [show realMatrixEnergy B u v = fun x ↦ ∑ i, ∑ j,
    Yau.coordPartial u x i*B x i j*Yau.coordPartial v x j from funext (realMatrixEnergy_apply B u v)]
  exact ContDiff.sum (fun i _ ↦ ContDiff.sum (fun j _ ↦
    ((real_coordPartial_smooth u hu i).mul (hB i j)).mul (real_coordPartial_smooth v hv j)))

lemma realMatrixEnergy_compact_left (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport u) : HasCompactSupport (realMatrixEnergy B u v) := by
  have hh := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦
    HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ ↦
      ((hc.fderiv_apply ℝ (Pi.single i 1)).mul_right (f' := fun x ↦ B x i j)).mul_right
        (f' := fun x ↦ Yau.coordPartial v x j)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (ext x; simp [realMatrixEnergy_apply,Yau.coordPartial])

lemma coordMatrixForm_symmetric (B : Matrix (Fin 4) (Fin 4) ℝ) (hs : ∀ i j, B i j = B j i)
    (v w : Yau.Jets.Coord) : coordMatrixForm B v w = coordMatrixForm B w v := by
  rw [coordMatrixForm_apply,coordMatrixForm_apply,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeightedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory
open scoped ContDiff
noncomputable section
variable {n : ℕ}

lemma real_pairing_compact (u : Coord n → ℝ) (V : Coord n → Coord n)
    (hc : HasCompactSupport u) : HasCompactSupport (pairing u V) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦
    (hc.fderiv_apply ℝ (Pi.single i 1)).mul_right (f' := fun x ↦ V x i))
  convert h using 1 <;> first | rfl | (ext x; simp [pairing,coordPartial])

lemma real_pairing_mul (u v : Coord n → ℝ) (V : Coord n → Coord n)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : Coord n) :
    pairing (fun y ↦ u y*v y) V x =
      v x*pairing u V x + u x*pairing v V x := by
  simp only [pairing,real_coordPartial_mul _ _ hu hv,add_mul,
    Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

lemma weightedSkewTransport_smooth (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (w : Coord n → ℝ) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (weightedSkewTransport gamma V w) :=
  (contDiff_const.mul (pairing_smooth hw hV)).add ((weightedDiv_smooth hg hgn hV).mul hw)

lemma weightedSkewTransport_compact (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (w : Coord n → ℝ) (hc : HasCompactSupport w) :
    HasCompactSupport (weightedSkewTransport gamma V w) :=
  ((real_pairing_compact w V hc).mul_left).add hc.mul_left

lemma compact_weighted_product_integrable (gamma u v : Coord n → ℝ)
    (hg : Continuous gamma) (hu : Continuous u) (hv : Continuous v)
    (hc : HasCompactSupport u) : Integrable (fun x ↦ gamma x*u x*v x) :=
  ((hg.mul hu).mul hv).integrable_of_hasCompactSupport hc.mul_left.mul_right

theorem weighted_transport_green (gamma u v : Coord n → ℝ)
    (V : Coord n → Coord n) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport u)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    (∫ x, gamma x*u x*weightedSkewTransport gamma V v x) =
      -(∫ x, gamma x*weightedSkewTransport gamma V u x*v x) := by
  have hD := weightedDiv_smooth hg hgn hV
  have hpu := pairing_smooth hu hV
  have hpv := pairing_smooth hv hV
  have hi1 := compact_weighted_product_integrable gamma u (pairing v V)
    hg.continuous hu.continuous hpv.continuous hc
  have hi2 := compact_weighted_product_integrable gamma (pairing u V) v
    hg.continuous hpu.continuous hv.continuous (real_pairing_compact u V hc)
  have hi3 := compact_weighted_product_integrable gamma u (fun x ↦ v x*weightedDiv gamma V x)
    hg.continuous hu.continuous (hv.mul hD).continuous hc
  have he := (compact_weighted_integration_by_parts gamma (fun x ↦ u x*v x)
    hg hgn (hu.mul hv) hc.mul_right V hV).2.2
  have hpoint : (fun x ↦ gamma x*pairing (fun y ↦ u y*v y) V x) =
      (fun x ↦ gamma x*pairing u V x*v x + gamma x*u x*pairing v V x) := by
    funext x
    rw [real_pairing_mul u v V hu hv]
    ring
  rw [hpoint,integral_add hi2 hi1] at he
  have hpoint1 : (fun x ↦ gamma x*u x*weightedSkewTransport gamma V v x) =
      (fun x ↦ 2*(gamma x*u x*pairing v V x) + gamma x*u x*(v x*weightedDiv gamma V x)) := by
    funext x; unfold weightedSkewTransport; ring
  have hpoint2 : (fun x ↦ gamma x*weightedSkewTransport gamma V u x*v x) =
      (fun x ↦ 2*(gamma x*pairing u V x*v x) + gamma x*u x*(v x*weightedDiv gamma V x)) := by
    funext x; unfold weightedSkewTransport; ring
  rw [hpoint1,hpoint2,integral_add (hi1.const_mul 2) hi3,
    integral_add (hi2.const_mul 2) hi3,integral_const_mul,integral_const_mul]
  have heq : (fun x ↦ gamma x*(u x*v x)*weightedDiv gamma V x) =
      (fun x ↦ gamma x*u x*(v x*weightedDiv gamma V x)) := by funext x; ring
  rw [heq] at he
  linarith only [he]

lemma weightedSkewTransport_mul (gamma q v : Coord n → ℝ)
    (V : Coord n → Coord n) (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v)
    (x : Coord n) :
    weightedSkewTransport gamma V (fun y ↦ q y*v y) x =
      q x*weightedSkewTransport gamma V v x + 2*pairing q V x*v x := by
  unfold weightedSkewTransport
  rw [real_pairing_mul q v V hq hv]
  ring

theorem weighted_transport_multiplier (gamma q v : Coord n → ℝ)
    (V : Coord n → Coord n) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    (∫ x, gamma x*q x*v x*weightedSkewTransport gamma V v x) =
      -(∫ x, gamma x*pairing q V x*v x^2) := by
  have hT := weightedSkewTransport_smooth gamma V v hg hgn hV hv
  have hi1 := compact_weighted_product_integrable gamma (fun x ↦ q x*v x)
    (weightedSkewTransport gamma V v) hg.continuous (hq.mul hv).continuous hT.continuous hc.mul_left
  have hi2 := compact_weighted_product_integrable gamma (fun x ↦ v x*v x)
    (pairing q V) hg.continuous (hv.mul hv).continuous (pairing_smooth hq hV).continuous hc.mul_right
  have he := weighted_transport_green gamma (fun x ↦ q x*v x) v V hg hgn
    (hq.mul hv) hv hc.mul_left hV
  have heq : (fun x ↦ gamma x*weightedSkewTransport gamma V (fun y ↦ q y*v y) x*v x) =
      (fun x ↦ gamma x*(q x*v x)*weightedSkewTransport gamma V v x +
        2*(gamma x*(v x*v x)*pairing q V x)) := by
    funext x
    rw [weightedSkewTransport_mul gamma q v V hq hv]
    ring
  rw [heq,integral_add hi1 (hi2.const_mul 2),integral_const_mul] at he
  have heq1 : (fun x ↦ gamma x*q x*v x*weightedSkewTransport gamma V v x) =
      (fun x ↦ gamma x*(q x*v x)*weightedSkewTransport gamma V v x) := by funext x; ring
  have heq2 : (fun x ↦ gamma x*pairing q V x*v x^2) =
      (fun x ↦ gamma x*(v x*v x)*pairing q V x) := by funext x; ring
  rw [heq1,heq2]
  linarith only [he]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeightedElliptic
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix MeasureTheory
open scoped ContDiff
noncomputable section

lemma realMatrixFlux_smooth (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (w : Yau.Jets.Coord → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hw : ContDiff ℝ ∞ w) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ realMatrixFlux B w x i) :=
  ContDiff.sum (fun j _ ↦ (hB i j).mul (Yau.real_coordPartial_smooth w hw j))

lemma realMatrixFlux_compact (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (w : Yau.Jets.Coord → ℝ)
    (hc : HasCompactSupport w) (i : Fin 4) : HasCompactSupport (fun x ↦ realMatrixFlux B w x i) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ ↦
    (hc.fderiv_apply ℝ (Pi.single j 1)).mul_left (f := fun x ↦ B x i j))
  exact h

lemma realWeightedElliptic_smooth (gamma : Yau.Jets.Coord → ℝ) (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (w : Yau.Jets.Coord → ℝ) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (realWeightedElliptic gamma B w) :=
  Yau.weightedDiv_smooth hg hgn (realMatrixFlux_smooth B w hB hw)

lemma realWeightedElliptic_compact (gamma : Yau.Jets.Coord → ℝ) (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (w : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport w) : HasCompactSupport (realWeightedElliptic gamma B w) := by
  have h := (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦
    ((realMatrixFlux_compact B w hc i).mul_left (f := gamma)).fderiv_apply ℝ (Pi.single i 1))).mul_left
      (f := fun x ↦ (gamma x)⁻¹)
  exact h

lemma realMatrixEnergy_pairing (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    Yau.pairing u (realMatrixFlux B v) x = realMatrixEnergy B u v x := by
  simp only [Yau.pairing,realMatrixFlux,realMatrixEnergy_apply,Finset.mul_sum,mul_assoc]

lemma realMatrixEnergy_symmetric (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀ x i j, B x i j = B x j i) (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B u v x = realMatrixEnergy B v u x :=
  coordMatrixForm_symmetric (B x) (hs x) _ _

theorem real_weighted_elliptic_green (gamma : Yau.Jets.Coord → ℝ) (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport u) :
    Integrable (fun x ↦ gamma x*realMatrixEnergy B u v x) ∧
    Integrable (fun x ↦ gamma x*u x*realWeightedElliptic gamma B v x) ∧
    (∫ x, gamma x*u x*realWeightedElliptic gamma B v x) =
      -(∫ x, gamma x*realMatrixEnergy B u v x) := by
  obtain ⟨hiE,hiL,he⟩ := Yau.compact_weighted_integration_by_parts gamma u hg hgn hu hc
    (realMatrixFlux B v) (realMatrixFlux_smooth B v hB hv)
  simp only [realMatrixEnergy_pairing] at hiE he
  refine ⟨hiE,hiL,?_⟩
  change (∫ x, gamma x*u x*Yau.weightedDiv gamma (realMatrixFlux B v) x) = _
  linarith only [he]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealEllipticLocalityLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Filter
open scoped Topology ContDiff

lemma realCoordPartial_eventuallyEq {f g : Yau.Jets.Coord → ℝ} {x : Yau.Jets.Coord}
    (h : f =ᶠ[𝓝 x] g) (i : Fin 4) :
    (fun y ↦ Yau.coordPartial f y i) =ᶠ[𝓝 x] (fun y ↦ Yau.coordPartial g y i) := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp only [Yau.coordPartial,hy]

lemma realWeightedElliptic_eventuallyEq (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    {f g : Yau.Jets.Coord → ℝ} {x : Yau.Jets.Coord} (h : f =ᶠ[𝓝 x] g) :
    realWeightedElliptic gamma B f =ᶠ[𝓝 x] realWeightedElliptic gamma B g := by
  have hflux (i : Fin 4) :
      (fun y ↦ gamma y*realMatrixFlux B f y i) =ᶠ[𝓝 x]
        (fun y ↦ gamma y*realMatrixFlux B g y i) := by
    filter_upwards [eventually_all.mpr (fun j ↦ realCoordPartial_eventuallyEq h j)] with y hy
    simp only [realMatrixFlux,hy]
  filter_upwards [eventually_all.mpr (fun i ↦ realCoordPartial_eventuallyEq (hflux i) i)] with y hy
  simp only [realWeightedElliptic,Yau.weightedDiv,Yau.coordDiv,hy]

lemma realWeightedElliptic_zero (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) :
    realWeightedElliptic gamma B (fun _ ↦ 0) = 0 := by
  have h : realMatrixFlux B (fun _ ↦ 0) = fun _ _ ↦ 0 := by
    funext x i; simp [realMatrixFlux,Yau.coordPartial]
  funext x
  simp [realWeightedElliptic,h,Yau.weightedDiv,Yau.coordDiv,Yau.coordPartial]

lemma realEllipticResidual_eventuallyEq (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    {f g : Yau.Jets.Coord → ℝ} {x : Yau.Jets.Coord} (h : f =ᶠ[𝓝 x] g) :
    realEllipticResidual gamma potential B f =ᶠ[𝓝 x] realEllipticResidual gamma potential B g := by
  filter_upwards [realWeightedElliptic_eventuallyEq gamma B h,h] with y hL hy
  simp only [realEllipticResidual,hL,hy]

lemma realEllipticResidual_zero (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) :
    realEllipticResidual gamma potential B (fun _ ↦ 0) = 0 := by
  funext x; simp [realEllipticResidual,realWeightedElliptic_zero]

lemma realEllipticResidual_tsupport (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (f : Yau.Jets.Coord → ℝ) :
    tsupport (realEllipticResidual gamma potential B f) ⊆ tsupport f := by
  intro x hx
  by_contra hn
  have he := realEllipticResidual_eventuallyEq gamma potential B
    (notMem_tsupport_iff_eventuallyEq.mp hn)
  change realEllipticResidual gamma potential B f =ᶠ[𝓝 x]
    realEllipticResidual gamma potential B (fun _ ↦ 0) at he
  rw [realEllipticResidual_zero] at he
  exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx

lemma realEllipticResidual_smooth (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (f : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0) (hp : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (realEllipticResidual gamma potential B f) :=
  (realWeightedElliptic_smooth gamma B f hg hgn hB hf).add (hp.mul hf)

lemma realEllipticResidual_compact (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (f : Yau.Jets.Coord → ℝ)
    (hc : HasCompactSupport f) : HasCompactSupport (realEllipticResidual gamma potential B f) :=
  (realWeightedElliptic_compact gamma B f hc).add hc.mul_left

open Matrix MeasureTheory
open scoped ContDiff

theorem real_weighted_square_identity
    (gamma q v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (t : ℝ) :
    (∫ x, gamma x*(realWeightedElliptic gamma B v x + t^2*q x*v x -
        t*Yau.weightedSkewTransport gamma V v x)^2) =
      (∫ x, gamma x*(realWeightedElliptic gamma B v x + t^2*q x*v x)^2) +
      t^2*(∫ x, gamma x*(Yau.weightedSkewTransport gamma V v x)^2) +
      2*t*(∫ x, gamma x*realMatrixEnergy B (Yau.weightedSkewTransport gamma V v) v x) +
      2*t^3*(∫ x, gamma x*Yau.pairing q V x*v x^2) := by
  let L := realWeightedElliptic gamma B v
  let T := Yau.weightedSkewTransport gamma V v
  let S := fun x ↦ L x+t^2*q x*v x
  have hL : ContDiff ℝ ∞ L := realWeightedElliptic_smooth gamma B v hg hgn hB hv
  have hLc : HasCompactSupport L := realWeightedElliptic_compact gamma B v hc
  have hT : ContDiff ℝ ∞ T := Yau.weightedSkewTransport_smooth gamma V v hg hgn hV hv
  have hTc : HasCompactSupport T := Yau.weightedSkewTransport_compact gamma V v hc
  have hS : ContDiff ℝ ∞ S := hL.add ((contDiff_const.mul hq).mul hv)
  have hSc : HasCompactSupport S := hLc.add hc.mul_left
  have hcS2 : HasCompactSupport (fun x ↦ S x^2) := by
    convert hSc.mul_right (f' := S) using 1 <;> first | rfl | (ext x; simp [pow_two])
  have hcT2 : HasCompactSupport (fun x ↦ T x^2) := by
    convert hTc.mul_right (f' := T) using 1 <;> first | rfl | (ext x; simp [pow_two])
  have hiS : Integrable (fun x ↦ gamma x*(S x)^2) :=
    (hg.mul (hS.pow 2)).continuous.integrable_of_hasCompactSupport hcS2.mul_left
  have hiT : Integrable (fun x ↦ gamma x*(T x)^2) :=
    (hg.mul (hT.pow 2)).continuous.integrable_of_hasCompactSupport hcT2.mul_left
  have hiTL := Yau.compact_weighted_product_integrable gamma T L hg.continuous hT.continuous hL.continuous hTc
  have hiq : Integrable (fun x ↦ gamma x*q x*v x*T x) :=
    (((hg.mul hq).mul hv).mul hT).continuous.integrable_of_hasCompactSupport hc.mul_left.mul_right
  have hexpand : (fun x ↦ gamma x*(L x+t^2*q x*v x-t*T x)^2) =
      (fun x ↦ ((gamma x*(S x)^2 + t^2*(gamma x*(T x)^2)) -
        2*t*(gamma x*T x*L x)) - 2*t^3*(gamma x*q x*v x*T x)) := by
    funext x; dsimp [S] <;> ring
  change (∫ x, gamma x*(L x+t^2*q x*v x-t*T x)^2) = _
  rw [hexpand,integral_sub
      (f := fun x ↦ gamma x*(S x)^2 + t^2*(gamma x*(T x)^2) - 2*t*(gamma x*T x*L x))
      (g := fun x ↦ 2*t^3*(gamma x*q x*v x*T x))
      ((hiS.add (hiT.const_mul (t^2))).sub (hiTL.const_mul (2*t)))
      (hiq.const_mul (2*t^3)),
    integral_sub (f := fun x ↦ gamma x*(S x)^2 + t^2*(gamma x*(T x)^2))
      (g := fun x ↦ 2*t*(gamma x*T x*L x))
      (hiS.add (hiT.const_mul (t^2))) (hiTL.const_mul (2*t)),
    integral_add hiS (hiT.const_mul (t^2))]
  simp only [integral_const_mul]
  have hgreen := (real_weighted_elliptic_green gamma B T v hg hgn hB hT hv hTc).2.2
  have hmult := Yau.weighted_transport_multiplier gamma q v V hg hgn hq hv hc hV
  change (∫ x, gamma x*T x*L x) = _ at hgreen
  change (∫ x, gamma x*q x*v x*T x) = _ at hmult
  rw [hgreen,hmult]
  change (∫ x, gamma x*(S x)^2) + _ - _ - _ = (∫ x, gamma x*(S x)^2) + _ + _ + _
  ring

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealEllipticProducts
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

theorem realWeightedElliptic_complex (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (w : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hw : ContDiff ℝ ∞ w)
    (x : Yau.Jets.Coord) :
    (realWeightedElliptic gamma B w x : ℂ) =
      Yau.Jets.smoothSecondOrder (fun i j y ↦ (B y i j : ℂ))
        (fun j y ↦ (Yau.realEllipticDrift gamma B y j : ℂ)) (fun y ↦ (w y : ℂ)) x := by
  have hd (j : Fin 4) : Yau.Jets.coordPartial j (fun y ↦ (w y : ℂ)) =
      fun y ↦ (Yau.coordPartial w y j : ℂ) :=
    funext (fun y ↦ coordPartial_ofReal_at w y (hw.differentiable (by simp) y) j)
  unfold realWeightedElliptic realMatrixFlux
  rw [Yau.real_weighted_elliptic_expansion gamma hg hgn B hB w hw]
  simp only [Yau.Jets.smoothSecondOrder,hd]
  simp_rw [coordPartial_ofReal_at _ x
    ((Yau.real_coordPartial_smooth w hw _).differentiable (by simp) x)]
  simp only [Yau.coordPartial,Complex.ofReal_add,Complex.ofReal_sum,Complex.ofReal_mul]

lemma realMatrixEnergy_cross_sum (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀ x i j, B x i j = B x j i) (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    (∑ i, ∑ j, B x i j*(Yau.coordPartial u x i*Yau.coordPartial v x j +
      Yau.coordPartial u x j*Yau.coordPartial v x i)) = 2*realMatrixEnergy B u v x := by
  have hswap : (∑ i, ∑ j, B x i j*Yau.coordPartial u x j*Yau.coordPartial v x i) =
      (∑ i, ∑ j, B x i j*Yau.coordPartial u x i*Yau.coordPartial v x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hs x j i]
  simp only [mul_add,← mul_assoc,Finset.sum_add_distrib,hswap,realMatrixEnergy_apply]
  simp only [mul_assoc,mul_comm]
  ring

theorem real_weighted_elliptic_product (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (u v : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : Yau.Jets.Coord) :
    realWeightedElliptic gamma B (fun y ↦ u y*v y) x =
      u x*realWeightedElliptic gamma B v x + v x*realWeightedElliptic gamma B u x +
      2*realMatrixEnergy B u v x := by
  have h := Yau.Jets.smoothSecondOrder_mul (fun i j y ↦ (B y i j : ℂ))
    (fun j y ↦ (Yau.realEllipticDrift gamma B y j : ℂ))
    (f := fun y ↦ (u y:ℂ)) (u := fun y ↦ (v y:ℂ))
    (Complex.ofRealCLM.contDiff.comp hu) (Complex.ofRealCLM.contDiff.comp hv) x
  have hp : (fun y ↦ (u y:ℂ)*(v y:ℂ)) = fun y ↦ ((u y*v y:ℝ):ℂ) := by
    funext y; simp only [Complex.ofReal_mul]
  change Yau.Jets.smoothSecondOrder _ _ (fun y ↦ (u y:ℂ)*(v y:ℂ)) x = _ at h
  rw [hp,← realWeightedElliptic_complex gamma B _ hg hgn hB (hu.mul hv),
    ← realWeightedElliptic_complex gamma B v hg hgn hB hv,
    ← realWeightedElliptic_complex gamma B u hg hgn hB hu] at h
  simp only [coordPartial_ofReal_at u x (hu.differentiable (by simp) x),
    coordPartial_ofReal_at v x (hv.differentiable (by simp) x)] at h
  have hreal : realWeightedElliptic gamma B (fun y ↦ u y*v y) x =
      u x*realWeightedElliptic gamma B v x + v x*realWeightedElliptic gamma B u x +
      ∑ i, ∑ j, B x i j*(Yau.coordPartial u x i*Yau.coordPartial v x j +
        Yau.coordPartial u x j*Yau.coordPartial v x i) := by
    exact_mod_cast h
  rw [realMatrixEnergy_cross_sum B hs u v] at hreal
  exact hreal

theorem real_weighted_elliptic_exp (gamma phi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hphi : ContDiff ℝ ∞ phi) (t : ℝ) (x : Yau.Jets.Coord) :
    realWeightedElliptic gamma B (fun y ↦ Real.exp (t*phi y)) x =
      (t*realWeightedElliptic gamma B phi x + t^2*realMatrixEnergy B phi phi x)*Real.exp (t*phi x) := by
  have he : Yau.Jets.waveExp (fun y ↦ (phi y:ℂ)) t = fun y ↦ (Real.exp (t*phi y):ℂ) := by
    funext y
    simp only [Yau.Jets.waveExp,← Complex.ofReal_mul,Complex.ofReal_exp]
  have h := Yau.Jets.smoothSecondOrder_waveExp (fun i j y ↦ (B y i j:ℂ))
    (fun j y ↦ (Yau.realEllipticDrift gamma B y j:ℂ))
    (phi := fun y ↦ (phi y:ℂ)) (Complex.ofRealCLM.contDiff.comp hphi) t x
  change Yau.Jets.smoothSecondOrder _ _ (Yau.Jets.waveExp (fun y ↦ (phi y:ℂ)) t) x = _ at h
  rw [he,← realWeightedElliptic_complex gamma B _ hg hgn hB ((contDiff_const.mul hphi).exp),
    ← realWeightedElliptic_complex gamma B phi hg hgn hB hphi] at h
  simp only [Yau.Jets.smoothEikonal,add_sub_cancel_right,
    coordPartial_ofReal_at phi x (hphi.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)] at h
  have heik : (∑ i, ∑ j, (B x i j:ℂ)*
      (Yau.coordPartial phi x i:ℂ)*(Yau.coordPartial phi x j:ℂ)) =
      (realMatrixEnergy B phi phi x:ℂ) := by
    simp only [realMatrixEnergy_apply,Complex.ofReal_sum,Complex.ofReal_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  change _ = (((t:ℂ)*(realWeightedElliptic gamma B phi x:ℂ) + (t:ℂ)^2*
    (∑ i, ∑ j, (B x i j:ℂ)*(Yau.coordPartial phi x i:ℂ)*(Yau.coordPartial phi x j:ℂ)))*
      (Real.exp (t*phi x):ℂ)) at h
  rw [heik] at h
  exact_mod_cast h

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_RealCutoffResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Metric
open scoped Topology ContDiff
noncomputable section

lemma real_cutoff_residual_location (gamma potential eta W psi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hpsi : Continuous psi) (x0 : Yau.Jets.Coord) (R s : ℝ)
    (heta : tsupport eta ⊆ ball x0 R)
    (heta1 : ∀ x ∈ closedBall x0 s, eta =ᶠ[𝓝 x] (fun _ ↦ 1))
    (hEq : ∀ x ∈ ball x0 R, realEllipticResidual gamma potential B W x = 0)
    (hzero : ∀ x ∈ ball x0 R, 0 < psi x → W x = 0) :
    ∀ x, realEllipticResidual gamma potential B (fun y ↦ eta y*W y) x ≠ 0 →
      x ∈ ball x0 R ∧ s ≤ dist x x0 ∧ psi x ≤ 0 := by
  intro x hx
  have hxs : x ∈ tsupport eta := tsupport_mul_subset_left
    (realEllipticResidual_tsupport gamma potential B (fun y ↦ eta y*W y) (subset_tsupport _ hx))
  have hxR := heta hxs
  refine ⟨hxR,?_,?_⟩
  · by_contra hn
    have hd : x ∈ closedBall x0 s := mem_closedBall.mpr (not_le.mp hn).le
    have he : (fun y ↦ eta y*W y) =ᶠ[𝓝 x] W := by
      filter_upwards [heta1 x hd] with y hy
      simp only [hy,one_mul]
    exact hx ((realEllipticResidual_eventuallyEq gamma potential B he).self_of_nhds.trans (hEq x hxR))
  · by_contra hn
    have hp : 0 < psi x := not_le.mp hn
    have he : (fun y ↦ eta y*W y) =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      filter_upwards [isOpen_ball.mem_nhds hxR,hpsi.continuousAt.eventually (lt_mem_nhds hp)] with y hy hypsi
      simp only [hzero y hy hypsi,mul_zero]
    have hh := (realEllipticResidual_eventuallyEq gamma potential B he).self_of_nhds
    rw [realEllipticResidual_zero] at hh
    exact hx hh

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactParameterEllipticityLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Metric
attribute [local instance] clmTopology clmAdd clmModule

theorem local_bilinear_coercivity
    (g : Yau.Jets.Coord → Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ)
    (hg : Continuous g) (x0 : Yau.Jets.Coord)
    (hp : ∀ v : Yau.Jets.Coord, v ≠ 0 → 0 < g x0 v v) :
    ∃ r > 0, ∃ a > 0, ∀ x ∈ ball x0 r, ∀ v : Yau.Jets.Coord,
      a*(∑ i, (v i)^2) ≤ g x v v := by
  obtain ⟨c,hc,C,hC,hbase⟩ := uniform_metric_coercivity (fun _ : Unit ↦ g x0)
    continuous_const (fun _ v hv ↦ hp v hv)
  obtain ⟨r,hr,hnear⟩ := Metric.continuousAt_iff.mp (hg.continuousAt (x := x0)) (c/2) (by positivity)
  refine ⟨r,hr,c/8,by positivity,?_⟩
  intro x hx v
  have hn : ‖g x-g x0‖ ≤ c/2 := by
    exact (show ‖g x-g x0‖ < c/2 from by simpa only [dist_eq_norm] using hnear hx).le
  have habs : |g x v v-g x0 v v| ≤ (c/2)*‖v‖^2 := by
    have h := bilinear_pairing_bound (g x-g x0) v v
    simp only [_root_.sub_apply] at h
    exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_right hn (sq_nonneg ‖v‖)])
  have hb := (hbase ()).2 v
  have hs := mul_le_mul_of_nonneg_left (coord_sum_sq_le_four_norm_sq v) hc.le
  have hlo := (abs_le.mp habs).1
  change c*‖v‖^2 ≤ g x0 v v at hb
  nlinarith only [hb,hs,hlo]

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ExponentialIntegralSeparation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter MeasureTheory
open scoped Topology
noncomputable section

theorem exponential_integral_separation (F G phi : Yau.Jets.Coord → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hphi : Continuous phi)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (c T : ℝ) (hgap : ∀ x, G x ≠ 0 → phi x ≤ c)
    (hbound : ∀ t : ℝ, T ≤ t →
      (∫ x, Real.exp (t*phi x)*F x) ≤ (∫ x, Real.exp (t*phi x)*G x)) :
    ∀ y, c < phi y → F y = 0 := by
  intro y hy
  by_contra hFy
  let d := (c+phi y)/2
  have hcd : c < d := by dsimp [d] <;> linarith
  have hdy : d < phi y := by dsimp [d] <;> linarith
  let theta := fun x ↦ min 1 (max 0 (phi x-d))
  let H := fun x ↦ theta x*F x
  have htheta : Continuous theta := continuous_const.min (continuous_const.max (hphi.sub continuous_const))
  have ht0 (x) : 0 ≤ theta x := le_min zero_le_one (le_max_left _ _)
  have ht1 (x) : theta x ≤ 1 := min_le_left _ _
  have hH : Continuous H := htheta.mul hF
  have hcH : HasCompactSupport H := hcF.mul_left
  have hH0 (x) : 0 ≤ H x := mul_nonneg (ht0 x) (hF0 x)
  have hHy : H y ≠ 0 := mul_ne_zero (ne_of_gt (lt_min zero_lt_one
    (lt_max_of_lt_right (sub_pos.mpr hdy)))) hFy
  have hI : 0 < ∫ x, H x := hH.integral_pos_of_hasCompactSupport_nonneg_nonzero hcH hH0 hHy
  have hiH := hH.integrable_of_hasCompactSupport hcH (μ := volume)
  have hiG := hG.integrable_of_hasCompactSupport hcG (μ := volume)
  have hmain (t : ℝ) (ht : max T 0 ≤ t) :
      (∫ x, H x) ≤ Real.exp (-(d-c)*t)*(∫ x, G x) := by
    have ht0' : 0 ≤ t := (le_max_right _ _).trans ht
    have hiFt : Integrable (fun x ↦ Real.exp (t*phi x)*F x) :=  ((Real.continuous_exp.comp (continuous_const.mul hphi)).mul hF).integrable_of_hasCompactSupport
      hcF.mul_left (μ := volume)
    have hiGt : Integrable (fun x ↦ Real.exp (t*phi x)*G x) :=  ((Real.continuous_exp.comp (continuous_const.mul hphi)).mul hG).integrable_of_hasCompactSupport
      hcG.mul_left (μ := volume)
    have hlow (x) : Real.exp (t*d)*H x ≤ Real.exp (t*phi x)*F x := by
      by_cases hx : phi x ≤ d
      · have hzero : theta x = 0 := by simp [theta,max_eq_left (sub_nonpos.mpr hx)]
        change Real.exp (t*d)*(theta x*F x) ≤ _
        rw [hzero,zero_mul,mul_zero]
        exact mul_nonneg (Real.exp_pos _).le (hF0 x)
      · have he : Real.exp (t*d) ≤ Real.exp (t*phi x) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (not_le.mp hx).le ht0')
        calc
          _ ≤ Real.exp (t*d)*F x := mul_le_mul_of_nonneg_left
            (by dsimp [H]; nlinarith only [ht1 x,hF0 x]) (Real.exp_pos _).le
          _ ≤ _ := mul_le_mul_of_nonneg_right he (hF0 x)
    have hupp (x) : Real.exp (t*phi x)*G x ≤ Real.exp (t*c)*G x := by
      by_cases hx : G x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hgap x hx) ht0')) (hG0 x)
    have hl := integral_mono (hiH.const_mul (Real.exp (t*d))) hiFt hlow
    have hu := integral_mono hiGt (hiG.const_mul (Real.exp (t*c))) hupp
    rw [integral_const_mul] at hl hu
    have hb := hbound t ((le_max_left _ _).trans ht)
    have hh : Real.exp (t*d)*(∫ x, H x) ≤ Real.exp (t*c)*(∫ x, G x) := hl.trans (hb.trans hu)
    have heq : Real.exp (-(d-c)*t)*Real.exp (t*d) = Real.exp (t*c) := by
      rw [← Real.exp_add]; congr 1; ring
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (t*d))).mp
    calc
      _ = Real.exp (t*d)*(∫ x, H x) := by ring
      _ ≤ Real.exp (t*c)*(∫ x, G x) := hh
      _ = _ := by rw [← heq]; ring
  have hdec : Tendsto (fun t : ℝ ↦ Real.exp (-(d-c)*t)*(∫ x, G x)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos (sub_pos.mpr hcd))).mpr
        (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
    simpa only [Function.comp_def,zero_mul,id_eq] using he.mul_const (∫ x, G x)
  have hle : (∫ x, H x) ≤ 0 := ge_of_tendsto hdec
    ((eventually_ge_atTop (max T 0)).mono (fun t ht ↦ hmain t ht))
  exact (not_le_of_gt hI) hle

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealTransportDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open scoped ContDiff
noncomputable section
variable {n : ℕ}

lemma real_coordPartial_commute (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u)
    (x : Coord n) (i j : Fin n) :
    coordPartial (fun y ↦ coordPartial u y j) x i =
      coordPartial (fun y ↦ coordPartial u y i) x j := by
  have hd := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  unfold coordPartial
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.comp_zero,
    ContinuousLinearMap.flip_apply,zero_add]
  exact hu.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _ _

lemma real_coordPartial_pairing (u : Coord n → ℝ) (V : Coord n → Coord n)
    (hu : ContDiff ℝ ∞ u) (hV : ∀ k, ContDiff ℝ ∞ (fun x ↦ V x k))
    (x : Coord n) (i : Fin n) :
    coordPartial (pairing u V) x i =
      ∑ k, (coordPartial (fun y ↦ coordPartial u y k) x i*V x k +
        coordPartial u x k*coordPartial (fun y ↦ V y k) x i) := by
  unfold pairing
  rw [real_coordPartial_sum _ (fun k ↦ (real_coordPartial_smooth u hu k).mul (hV k))]
  simp only [real_coordPartial_mul _ _ (real_coordPartial_smooth u hu _) (hV _)]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMatrixTransport
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

lemma realMatrixEnergy_derivative (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (v : Yau.Jets.Coord → ℝ) (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hs : ∀ x i j, B x i j = B x j i) (hv : ContDiff ℝ ∞ v)
    (x : Yau.Jets.Coord) (k : Fin 4) :
    Yau.coordPartial (realMatrixEnergy B v v) x k =
      (∑ i, ∑ j, Yau.coordPartial (fun y ↦ B y i j) x k *
        Yau.coordPartial v x i*Yau.coordPartial v x j) +
      2*(∑ i, ∑ j, B x i j*Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k*
        Yau.coordPartial v x j) := by
  have hvd := Yau.real_coordPartial_smooth v hv
  have he : realMatrixEnergy B v v = fun y ↦ ∑ i, ∑ j,
      Yau.coordPartial v y i*B y i j*Yau.coordPartial v y j :=
    funext (realMatrixEnergy_apply B v v)
  rw [he,Yau.real_coordPartial_sum _ (fun i ↦
    ContDiff.sum (fun j _ ↦ ((hvd i).mul (hB i j)).mul (hvd j)))]
  simp_rw [Yau.real_coordPartial_sum _ (fun j ↦ ((hvd _).mul (hB _ j)).mul (hvd j)),
    Yau.real_coordPartial_mul _ _ ((hvd _).mul (hB _ _)) (hvd _),
    Yau.real_coordPartial_mul _ _ (hvd _) (hB _ _)]
  have hswap : (∑ i, ∑ j, Yau.coordPartial v x i*B x i j*
      Yau.coordPartial (fun y ↦ Yau.coordPartial v y j) x k) =
      (∑ i, ∑ j, B x i j*Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k*
        Yau.coordPartial v x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs x j i]
    ring
  simp only [add_mul,Finset.sum_add_distrib]
  rw [hswap]
  have ha : (∑ i, ∑ j, Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k * B x i j *
      Yau.coordPartial v x j) =
      (∑ i, ∑ j, B x i j*Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k*
        Yau.coordPartial v x j) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  have hb : (∑ i, ∑ j, Yau.coordPartial v x i*Yau.coordPartial (fun y ↦ B y i j) x k*
      Yau.coordPartial v x j) =
      (∑ i, ∑ j, Yau.coordPartial (fun y ↦ B y i j) x k *
        Yau.coordPartial v x i*Yau.coordPartial v x j) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  rw [ha,hb]
  ring

lemma real_sum_rotate (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ k, ∑ i, ∑ j, f k i j) = ∑ i, ∑ j, ∑ k, f k i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem realMatrixEnergy_transport (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ k, ContDiff ℝ ∞ (fun x ↦ V x k)) (hv : ContDiff ℝ ∞ v) (x : Yau.Jets.Coord) :
    2*realMatrixEnergy B (Yau.pairing v V) v x =
      Yau.pairing (realMatrixEnergy B v v) V x + realTransportDeformation B V v x := by
  have he : Yau.pairing (realMatrixEnergy B v v) V x =
      (∑ i, ∑ j, ∑ k, (Yau.coordPartial (fun y ↦ B y i j) x k *
        Yau.coordPartial v x i*Yau.coordPartial v x j)*V x k) +
      (∑ i, ∑ j, ∑ k, (2*(B x i j*Yau.coordPartial (fun y ↦ Yau.coordPartial v y i) x k*
        Yau.coordPartial v x j))*V x k) := by
    simp only [Yau.pairing,realMatrixEnergy_derivative B v hB hs hv,add_mul,
      Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
    congr 1 <;> exact real_sum_rotate _
  rw [realMatrixEnergy_apply,he]
  simp_rw [Yau.real_coordPartial_pairing v V hv hV]
  simp only [add_mul,
    Finset.sum_add_distrib,Finset.sum_mul,realTransportDeformation,
    Finset.sum_sub_distrib]
  simp_rw [Yau.real_coordPartial_commute v hv x]
  simp only [mul_assoc,mul_left_comm,mul_comm]
  ring_nf
  simp only [← Finset.sum_mul]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMatrixEnergyProducts
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma realMatrixEnergy_add_left (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (f u v : Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ f y+u y) v x = realMatrixEnergy B f v x+realMatrixEnergy B u v x := by
  have he : realCoordGradient (fun y ↦ f y+u y) x = realCoordGradient f x+realCoordGradient u x := by
    ext i; exact Yau.real_coordPartial_add f u hf hu x i
  simp only [realMatrixEnergy,he,map_add,_root_.add_apply]

lemma realMatrixEnergy_mul_left (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (f u v : Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ f y*u y) v x =
      u x*realMatrixEnergy B f v x+f x*realMatrixEnergy B u v x := by
  have he : realCoordGradient (fun y ↦ f y*u y) x =
      u x • realCoordGradient f x+f x • realCoordGradient u x := by
    ext i
    simp only [realCoordGradient,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Yau.real_coordPartial_mul f u hf hu]
    ring
  simp only [realMatrixEnergy,he,map_add,map_smul,_root_.add_apply,_root_.smul_apply,smul_eq_mul]

lemma realMatrixEnergy_const_mul_left (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hu : ContDiff ℝ ∞ u) (a : ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ a*u y) v x = a*realMatrixEnergy B u v x := by
  have he : realCoordGradient (fun y ↦ a*u y) x = a • realCoordGradient u x := by
    ext i; exact Yau.real_coordPartial_const_mul u hu a x i
  simp only [realMatrixEnergy,he,map_smul,_root_.smul_apply,smul_eq_mul]

lemma realTransportDeformation_smooth (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hV : ∀ k, ContDiff ℝ ∞ (fun x ↦ V x k)) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (realTransportDeformation B V v) := by
  apply ContDiff.sum; intro i _
  apply ContDiff.sum; intro j _
  apply ContDiff.sum; intro k _
  exact ((((contDiff_const.mul (hB i j)).mul (Yau.real_coordPartial_smooth _ (hV k) i)).mul
    (Yau.real_coordPartial_smooth v hv k)).mul (Yau.real_coordPartial_smooth v hv j)).sub
      ((((hV k).mul (Yau.real_coordPartial_smooth _ (hB i j) k)).mul
        (Yau.real_coordPartial_smooth v hv i)).mul (Yau.real_coordPartial_smooth v hv j))

lemma realTransportDeformation_compact (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ)
    (hc : HasCompactSupport v) : HasCompactSupport (realTransportDeformation B V v) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦
    HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ ↦
    HasCompactSupport.finset_sum (s := Finset.univ) (fun k _ ↦
      ((hc.fderiv_apply ℝ (Pi.single j 1)).mul_left
        (f := fun x ↦ 2*B x i j*Yau.coordPartial (fun y ↦ V y k) x i*Yau.coordPartial v x k)).sub
      ((hc.fderiv_apply ℝ (Pi.single j 1)).mul_left
        (f := fun x ↦ V x k*Yau.coordPartial (fun y ↦ B y i j) x k*Yau.coordPartial v x i)))))
  exact h

theorem realMatrixEnergy_skew_transport (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (v : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ k, ContDiff ℝ ∞ (fun x ↦ V x k)) (hv : ContDiff ℝ ∞ v) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (Yau.weightedSkewTransport gamma V v) v x =
      Yau.pairing (realMatrixEnergy B v v) V x + realTransportDeformation B V v x +
      Yau.weightedDiv gamma V x*realMatrixEnergy B v v x +
      v x*realMatrixEnergy B (Yau.weightedDiv gamma V) v x := by
  unfold Yau.weightedSkewTransport
  rw [realMatrixEnergy_add_left _ _ _ _ (contDiff_const.mul (Yau.pairing_smooth hv hV))
      ((Yau.weightedDiv_smooth hg hgn hV).mul hv),
    realMatrixEnergy_const_mul_left _ _ _ (Yau.pairing_smooth hv hV),
    realMatrixEnergy_mul_left _ _ _ _ (Yau.weightedDiv_smooth hg hgn hV) hv,
    realMatrixEnergy_transport B V v hB hs hV hv]
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealTransportQuadratic
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

lemma realGradientSquare_smooth (v : Yau.Jets.Coord → ℝ) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (realGradientSquare v) :=
  ContDiff.sum (fun i _ ↦ (Yau.real_coordPartial_smooth v hv i).pow 2)

lemma realGradientSquare_compact (v : Yau.Jets.Coord → ℝ) (hc : HasCompactSupport v) :
    HasCompactSupport (realGradientSquare v) := by
  have hd (i : Fin 4) : HasCompactSupport (fun x ↦ (Yau.coordPartial v x i)^2) := by
    convert (hc.fderiv_apply ℝ (Pi.single i 1)).mul_right
      (f' := fun x ↦ Yau.coordPartial v x i) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext x; simp [pow_two,Yau.coordPartial])
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦ hd i)
  exact h

lemma realCoordGradient_zero_off_support (v : Yau.Jets.Coord → ℝ)
    {x : Yau.Jets.Coord} (hx : x ∉ tsupport v) : realCoordGradient v x = 0 := by
  ext i
  simp only [realCoordGradient,Yau.coordPartial,fderiv_of_notMem_tsupport ℝ hx,
    _root_.zero_apply,Pi.zero_apply]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeightedCommutator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

theorem real_weighted_commutator_energy
    (gamma v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    2*(∫ x, gamma x*realMatrixEnergy B (Yau.weightedSkewTransport gamma V v) v x) =
      2*(∫ x, gamma x*realTransportDeformation B V v x) -
      (∫ x, gamma x*v x^2*realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x) := by
  let E := realMatrixEnergy B v v
  let r := Yau.weightedDiv gamma V
  let C := fun x ↦ gamma x*v x*realMatrixEnergy B r v x
  have hE : ContDiff ℝ ∞ E := realMatrixEnergy_smooth B hB v v hv hv
  have hEc : HasCompactSupport E := realMatrixEnergy_compact_left B v v hc
  have hr : ContDiff ℝ ∞ r := Yau.weightedDiv_smooth hg hgn hV
  have hiA : Integrable (fun x ↦ gamma x*Yau.pairing E V x) :=
    (hg.mul (Yau.pairing_smooth hE hV)).continuous.integrable_of_hasCompactSupport
      (Yau.real_pairing_compact E V hEc).mul_left
  have hiD : Integrable (fun x ↦ gamma x*realTransportDeformation B V v x) :=
    (hg.mul (realTransportDeformation_smooth B V v hB hV hv)).continuous.integrable_of_hasCompactSupport
      (realTransportDeformation_compact B V v hc).mul_left
  have hiR : Integrable (fun x ↦ gamma x*r x*E x) :=
    ((hg.mul hr).mul hE).continuous.integrable_of_hasCompactSupport hEc.mul_left
  have hiC : Integrable C := Yau.compact_weighted_product_integrable gamma v (realMatrixEnergy B r v)
    hg.continuous hv.continuous (realMatrixEnergy_smooth B hB r v hr hv).continuous hc
  have hzero := (Yau.compact_weighted_integration_by_parts gamma E hg hgn hE hEc V hV).2.2
  have hreorder : (fun x ↦ gamma x*E x*Yau.weightedDiv gamma V x) =
      (fun x ↦ gamma x*r x*E x) := by funext x; dsimp [r] <;> ring
  rw [hreorder] at hzero
  have hpoint : (fun x ↦ gamma x*realMatrixEnergy B (Yau.weightedSkewTransport gamma V v) v x) =
      (fun x ↦ ((gamma x*Yau.pairing E V x + gamma x*realTransportDeformation B V v x) +
        gamma x*r x*E x) + C x) := by
    funext x
    rw [realMatrixEnergy_skew_transport gamma B V v hg hgn hB hs hV hv]
    dsimp [E,r,C]
    ring
  have hcsq : HasCompactSupport (fun x ↦ v x^2) := by
    convert hc.mul_right (f' := v) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext point; simp [pow_two])
  have hgreen := (real_weighted_elliptic_green gamma B (fun x ↦ v x^2) r
    hg hgn hB (hv.pow 2) hr hcsq).2.2
  have hsquare : (fun x ↦ gamma x*realMatrixEnergy B (fun y ↦ v y^2) r x) =
      (fun x ↦ 2*C x) := by
    funext x
    rw [show (fun y ↦ v y^2) = (fun y ↦ v y*v y) by funext y; ring,
      realMatrixEnergy_mul_left B v v r hv hv,
      realMatrixEnergy_symmetric B hs v r]
    dsimp [C] <;> ring
  rw [hsquare,integral_const_mul] at hgreen
  rw [hpoint,integral_add
      (f := fun x ↦ gamma x*Yau.pairing E V x + gamma x*realTransportDeformation B V v x + gamma x*r x*E x)
      (g := C) ((hiA.add hiD).add hiR) hiC,
    integral_add (f := fun x ↦ gamma x*Yau.pairing E V x + gamma x*realTransportDeformation B V v x)
      (g := fun x ↦ gamma x*r x*E x) (hiA.add hiD) hiR,
    integral_add hiA hiD,hzero]
  change 2*((-(∫ x, gamma x*r x*E x)+(∫ x, gamma x*realTransportDeformation B V v x)) +
      (∫ x, gamma x*r x*E x)+(∫ x, C x)) =
      2*(∫ x, gamma x*realTransportDeformation B V v x) -
      (∫ x, gamma x*v x^2*realWeightedElliptic gamma B r x)
  linarith only [hgreen]

theorem real_weighted_commutator_identity
    (gamma q v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (t : ℝ) :
    (∫ x, gamma x*(realWeightedElliptic gamma B v x + t^2*q x*v x -
        t*Yau.weightedSkewTransport gamma V v x)^2) =
      (∫ x, gamma x*(realWeightedElliptic gamma B v x + t^2*q x*v x)^2) +
      t^2*(∫ x, gamma x*(Yau.weightedSkewTransport gamma V v x)^2) +
      2*t*(∫ x, gamma x*realTransportDeformation B V v x) -
      t*(∫ x, gamma x*v x^2*realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x) +
      2*t^3*(∫ x, gamma x*Yau.pairing q V x*v x^2) := by
  rw [real_weighted_square_identity gamma q v B V hg hgn hq hv hc hB hV]
  have he := real_weighted_commutator_energy gamma v B V hg hgn hv hc hB hs hV
  have he' := congrArg (fun z : ℝ ↦ t*z) he
  nlinarith only [he']

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeightedShift
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

theorem real_weighted_symmetric_shift (gamma q v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (t k : ℝ) :
    (∫ x, gamma x*(realWeightedElliptic gamma B v x+t^2*q x*v x)^2) =
      (∫ x, gamma x*(realWeightedElliptic gamma B v x+t^2*q x*v x+k*v x)^2) +
      2*k*(∫ x, gamma x*realMatrixEnergy B v v x) -
      2*k*t^2*(∫ x, gamma x*q x*v x^2) - k^2*(∫ x, gamma x*v x^2) := by
  let L := realWeightedElliptic gamma B v
  let S := fun x ↦ L x+t^2*q x*v x
  have hL := realWeightedElliptic_smooth gamma B v hg hgn hB hv
  have hLc := realWeightedElliptic_compact gamma B v hc
  have hS : ContDiff ℝ ∞ S := hL.add ((contDiff_const.mul hq).mul hv)
  have hSc : HasCompactSupport S := hLc.add hc.mul_left
  have hH : ContDiff ℝ ∞ (fun x ↦ S x+k*v x) := hS.add (contDiff_const.mul hv)
  have hHc : HasCompactSupport (fun x ↦ S x+k*v x) := hSc.add hc.mul_left
  have hHsq : HasCompactSupport (fun x ↦ (S x+k*v x)^2) := by
    convert hHc.mul_right (f' := fun point ↦ S point+k*v point) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext point; simp [pow_two])
  have hvsq : HasCompactSupport (fun x ↦ v x^2) := by
    convert hc.mul_right (f' := v) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext point; simp [pow_two])
  have hiH : Integrable (fun x ↦ gamma x*(S x+k*v x)^2) :=
    (hg.mul (hH.pow 2)).continuous.integrable_of_hasCompactSupport hHsq.mul_left
  have hiL := Yau.compact_weighted_product_integrable gamma v L hg.continuous hv.continuous hL.continuous hc
  have hiq : Integrable (fun x ↦ gamma x*q x*v x^2) :=
    ((hg.mul hq).mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hiv : Integrable (fun x ↦ gamma x*v x^2) :=
    (hg.mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hp : (fun x ↦ gamma x*(S x)^2) =
      (fun x ↦ ((gamma x*(S x+k*v x)^2-2*k*(gamma x*v x*L x)) -
        2*k*t^2*(gamma x*q x*v x^2)) - k^2*(gamma x*v x^2)) := by
    funext x; dsimp [S] <;> ring
  change (∫ x, gamma x*(S x)^2) = _
  rw [hp,integral_sub
      (f := fun x ↦ gamma x*(S x+k*v x)^2-2*k*(gamma x*v x*L x)-2*k*t^2*(gamma x*q x*v x^2))
      (g := fun x ↦ k^2*(gamma x*v x^2))
      ((hiH.sub (hiL.const_mul (2*k))).sub (hiq.const_mul (2*k*t^2))) (hiv.const_mul (k^2)),
    integral_sub (f := fun x ↦ gamma x*(S x+k*v x)^2-2*k*(gamma x*v x*L x))
      (g := fun x ↦ 2*k*t^2*(gamma x*q x*v x^2))
      (hiH.sub (hiL.const_mul (2*k))) (hiq.const_mul (2*k*t^2)),
    integral_sub hiH (hiL.const_mul (2*k))]
  simp only [integral_const_mul]
  have he := (real_weighted_elliptic_green gamma B v v hg hgn hB hv hv hc).2.2
  change (∫ x, gamma x*v x*L x) = _ at he
  rw [he]
  change (∫ x, gamma x*(S x+k*v x)^2) - _ - _ - _ = (∫ x, gamma x*(S x+k*v x)^2) + _ - _ - _
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCarlemanCoercivity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

theorem real_carleman_coercivity (gamma q v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i))
    (a b C s t : ℝ) (hC : 0 ≤ C) (ht : 1 ≤ t) (hlarge : C+s^2 ≤ b*t)
    (hquad : ∀ x ∈ tsupport v, ∀ xi : Yau.Jets.Coord,
      a*(∑ i, (xi i)^2) ≤ realTransportQuadratic B V x xi + s*coordMatrixForm (B x) xi xi)
    (hweight : ∀ x ∈ tsupport v, b ≤ Yau.pairing q V x-s*q x)
    (herror : ∀ x ∈ tsupport v,
      realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x ≤ C) :
    2*a*t*(∫ x, gamma x*realGradientSquare v x) + b*t^3*(∫ x, gamma x*v x^2) ≤
      (∫ x, gamma x*(realWeightedElliptic gamma B v x+t^2*q x*v x-
        t*Yau.weightedSkewTransport gamma V v x)^2) := by
  have hgn (x) := (hgp x).ne'
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hvsq : HasCompactSupport (fun x ↦ v x^2) := by
    convert hc.mul_right (f' := v) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext point; simp [pow_two])
  have hiv : Integrable (fun x ↦ gamma x*v x^2) :=
    (hg.mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hiq : Integrable (fun x ↦ gamma x*q x*v x^2) :=
    ((hg.mul hq).mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hiW : Integrable (fun x ↦ gamma x*Yau.pairing q V x*v x^2) :=
    ((hg.mul (Yau.pairing_smooth hq hV)).mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hvsq.mul_left
  have hiG : Integrable (fun x ↦ gamma x*realGradientSquare v x) :=
    (hg.mul (realGradientSquare_smooth v hv)).continuous.integrable_of_hasCompactSupport
      (realGradientSquare_compact v hc).mul_left
  have hiD : Integrable (fun x ↦ gamma x*realTransportDeformation B V v x) :=
    (hg.mul (realTransportDeformation_smooth B V v hB hV hv)).continuous.integrable_of_hasCompactSupport
      (realTransportDeformation_compact B V v hc).mul_left
  have hiE : Integrable (fun x ↦ gamma x*realMatrixEnergy B v v x) :=
    (hg.mul (realMatrixEnergy_smooth B hB v v hv hv)).continuous.integrable_of_hasCompactSupport
      (realMatrixEnergy_compact_left B v v hc).mul_left
  have hiR : Integrable (fun x ↦ gamma x*v x^2*realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x) :=
    ((hg.mul (hv.pow 2)).mul (realWeightedElliptic_smooth gamma B _ hg hgn hB
      (Yau.weightedDiv_smooth hg hgn hV))).continuous.integrable_of_hasCompactSupport hvsq.mul_left.mul_right
  have hDpoint (x : Yau.Jets.Coord) : a*realGradientSquare v x ≤
      realTransportDeformation B V v x+s*realMatrixEnergy B v v x := by
    by_cases hx : x ∈ tsupport v
    · exact hquad x hx (realCoordGradient v x)
    · have hz := realCoordGradient_zero_off_support v hx
      have hd (i) : Yau.coordPartial v x i = 0 := congrFun hz i
      simp [realGradientSquare,realTransportDeformation,realMatrixEnergy_apply,hd]
  have hDi := integral_mono (hiG.const_mul a) (hiD.add (hiE.const_mul s))
    (fun x ↦ show a*(gamma x*realGradientSquare v x) ≤
      gamma x*realTransportDeformation B V v x+s*(gamma x*realMatrixEnergy B v v x) by
        nlinarith only [mul_le_mul_of_nonneg_left (hDpoint x) (hgp x).le])
  simp only [Pi.add_apply] at hDi
  rw [integral_const_mul,integral_add hiD (hiE.const_mul s),integral_const_mul] at hDi
  have hWi := integral_mono (hiv.const_mul b) (hiW.sub (hiq.const_mul s))
    (fun x ↦ show b*(gamma x*v x^2) ≤ gamma x*Yau.pairing q V x*v x^2-s*(gamma x*q x*v x^2) by
      by_cases hx : x ∈ tsupport v
      · nlinarith only [mul_le_mul_of_nonneg_left (hweight x hx) (mul_nonneg (hgp x).le (sq_nonneg (v x)))]
      · simp [image_eq_zero_of_notMem_tsupport hx])
  simp only [Pi.sub_apply] at hWi
  rw [integral_const_mul,integral_sub hiW (hiq.const_mul s),integral_const_mul] at hWi
  have hRi := integral_mono hiR (hiv.const_mul C)
    (fun x ↦ show gamma x*v x^2*realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x ≤ C*(gamma x*v x^2) by
      by_cases hx : x ∈ tsupport v
      · nlinarith only [mul_le_mul_of_nonneg_left (herror x hx) (mul_nonneg (hgp x).le (sq_nonneg (v x)))]
      · simp [image_eq_zero_of_notMem_tsupport hx])
  rw [integral_const_mul] at hRi
  have hid := real_weighted_commutator_identity gamma q v B V hg hgn hq hv hc hB hs hV t
  rw [real_weighted_symmetric_shift gamma q v B hg hgn hq hv hc hB t (s*t)] at hid
  have hS0 : 0 ≤ ∫ x, gamma x*(realWeightedElliptic gamma B v x+t^2*q x*v x+s*t*v x)^2 :=
    integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
  have hT0 : 0 ≤ t^2*(∫ x, gamma x*(Yau.weightedSkewTransport gamma V v x)^2) :=
    mul_nonneg (sq_nonneg _) (integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _)))
  have hv0 : 0 ≤ ∫ x, gamma x*v x^2 := integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
  have hDm := mul_le_mul_of_nonneg_left hDi (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ht0)
  have hWm := mul_le_mul_of_nonneg_left hWi (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (pow_nonneg ht0 3))
  have hRm := mul_le_mul_of_nonneg_left hRi ht0
  have habs : s^2*t^2+C*t ≤ b*t^3 := by
    have h1 := mul_le_mul_of_nonneg_right hlarge ht0
    have h2 := mul_le_mul_of_nonneg_right h1 ht0
    have h3 := mul_nonneg hC (show 0 ≤ t^2-t by nlinarith only [ht])
    nlinarith only [h2,h3]
  have habsm := mul_le_mul_of_nonneg_right habs hv0
  nlinarith only [hid,hS0,hT0,hDm,hWm,hRm,habsm]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCarlemanConjugation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_coordPartial_exp (phi : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (t : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (fun y ↦ Real.exp (t*phi y)) x i =
      t*Real.exp (t*phi x)*Yau.coordPartial phi x i := by
  unfold Yau.coordPartial
  rw [(((contDiff_const.mul hphi).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt.exp).fderiv]
  rw [fderiv_fun_mul (differentiableAt_const _) (hphi.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
  simp
  ring

lemma realMatrixEnergy_exp (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (phi v : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (t : ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ Real.exp (t*phi y)) v x =
      t*Real.exp (t*phi x)*realMatrixEnergy B phi v x := by
  simp only [realMatrixEnergy_apply,real_coordPartial_exp phi hphi,Finset.mul_sum,mul_assoc]

theorem real_carleman_conjugation (gamma phi v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hphi : ContDiff ℝ ∞ phi) (hv : ContDiff ℝ ∞ v) (t : ℝ) (x : Yau.Jets.Coord) :
    Real.exp (t*phi x)*realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x =
      realWeightedElliptic gamma B v x + t^2*realMatrixEnergy B phi phi x*v x -
      t*Yau.weightedSkewTransport gamma (realMatrixFlux B phi) v x := by
  rw [real_weighted_elliptic_product gamma B _ v hg hgn hB hs ((contDiff_const.mul hphi).exp) hv,
    real_weighted_elliptic_exp gamma phi B hg hgn hB hphi,
    realMatrixEnergy_exp B phi v hphi,
    realMatrixEnergy_symmetric B hs phi v]
  have he : Real.exp (t*phi x)*Real.exp (-t*phi x) = 1 := by
    rw [← Real.exp_add,show t*phi x + -t*phi x = 0 by ring,Real.exp_zero]
  unfold Yau.weightedSkewTransport
  rw [realMatrixEnergy_pairing]
  change _ = realWeightedElliptic gamma B v x + t^2*realMatrixEnergy B phi phi x*v x -
    t*(2*realMatrixEnergy B v phi x+realWeightedElliptic gamma B phi x*v x)
  linear_combination (realWeightedElliptic gamma B v x + t^2*realMatrixEnergy B phi phi x*v x -
    t*(2*realMatrixEnergy B v phi x+realWeightedElliptic gamma B phi x*v x))*he

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCarlemanEstimate
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

variable (gamma phi v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hphi : ContDiff ℝ ∞ phi) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (a b C s t : ℝ) (hC : 0 ≤ C) (ht : 1 ≤ t) (hlarge : C+s^2 ≤ b*t)
    (hquad : ∀ x ∈ tsupport v, ∀ xi : Yau.Jets.Coord,
      a*(∑ i, (xi i)^2) ≤ realTransportQuadratic B (realMatrixFlux B phi) x xi +
        s*coordMatrixForm (B x) xi xi)
    (hweight : ∀ x ∈ tsupport v, b ≤
      Yau.pairing (realMatrixEnergy B phi phi) (realMatrixFlux B phi) x-s*realMatrixEnergy B phi phi x)
    (herror : ∀ x ∈ tsupport v,
      realWeightedElliptic gamma B (realWeightedElliptic gamma B phi) x ≤ C)

include hg hgp hB hs hphi hv hc hC ht hlarge hquad hweight herror

theorem real_carleman_estimate :
    2*a*t*(∫ x, gamma x*realGradientSquare v x) + b*t^3*(∫ x, gamma x*v x^2) ≤
      (∫ x, gamma x*(Real.exp (t*phi x)*realWeightedElliptic gamma B
        (fun y ↦ Real.exp (-t*phi y)*v y) x)^2) := by
  simp_rw [real_carleman_conjugation gamma phi v B hg (fun x ↦ (hgp x).ne') hB hs hphi hv]
  exact real_carleman_coercivity gamma (realMatrixEnergy B phi phi) v B (realMatrixFlux B phi)
    hg hgp (realMatrixEnergy_smooth B hB phi phi hphi hphi) hv hc hB hs
    (realMatrixFlux_smooth B phi hB hphi) a b C s t hC ht hlarge hquad hweight herror

theorem real_carleman_potential_estimate (potential : Yau.Jets.Coord → ℝ)
    (hpot : ContDiff ℝ ∞ potential) (M : ℝ)
    (hM : ∀ x ∈ tsupport v, (potential x)^2 ≤ M) (habs : 4*M ≤ b*t^3) :
    a*t*(∫ x, gamma x*realGradientSquare v x) + (b*t^3/4)*(∫ x, gamma x*v x^2) ≤
      (∫ x, gamma x*(Real.exp (t*phi x)*realWeightedElliptic gamma B
        (fun y ↦ Real.exp (-t*phi y)*v y) x + potential x*v x)^2) := by
  let P := fun x ↦ Real.exp (t*phi x)*realWeightedElliptic gamma B
    (fun y ↦ Real.exp (-t*phi y)*v y) x
  have hP : ContDiff ℝ ∞ P := (contDiff_const.mul hphi).exp.mul
    (realWeightedElliptic_smooth gamma B _ hg (fun x ↦ (hgp x).ne') hB
      (((contDiff_const.mul hphi).exp).mul hv))
  have hPc : HasCompactSupport P :=
    (realWeightedElliptic_compact gamma B _ hc.mul_left).mul_left
  have hF : ContDiff ℝ ∞ (fun x ↦ P x+potential x*v x) := hP.add (hpot.mul hv)
  have hFc : HasCompactSupport (fun x ↦ P x+potential x*v x) := hPc.add hc.mul_left
  have hP2 : HasCompactSupport (fun x ↦ (P x)^2) := by
    convert hPc.mul_right (f' := P) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext point; simp [pow_two])
  have hF2 : HasCompactSupport (fun x ↦ (P x+potential x*v x)^2) := by
    convert hFc.mul_right (f' := fun point ↦ P point+potential point*v point) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext point; simp [pow_two])
  have hv2 : HasCompactSupport (fun x ↦ v x^2) := by
    convert hc.mul_right (f' := v) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext point; simp [pow_two])
  have hiP : Integrable (fun x ↦ gamma x*(P x)^2) :=
    (hg.mul (hP.pow 2)).continuous.integrable_of_hasCompactSupport hP2.mul_left
  have hiF : Integrable (fun x ↦ gamma x*(P x+potential x*v x)^2) :=
    (hg.mul (hF.pow 2)).continuous.integrable_of_hasCompactSupport hF2.mul_left
  have hiv : Integrable (fun x ↦ gamma x*v x^2) :=
    (hg.mul (hv.pow 2)).continuous.integrable_of_hasCompactSupport hv2.mul_left
  have hpoint (x : Yau.Jets.Coord) : gamma x*(P x)^2 ≤
      2*(gamma x*(P x+potential x*v x)^2)+2*M*(gamma x*v x^2) := by
    have hMv : (potential x)^2*v x^2 ≤ M*v x^2 := by
      by_cases hx : x ∈ tsupport v
      · exact mul_le_mul_of_nonneg_right (hM x hx) (sq_nonneg _)
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have halg : (P x)^2 ≤ 2*(P x+potential x*v x)^2+2*M*v x^2 := by
      nlinarith only [hMv,sq_nonneg (P x+2*potential x*v x)]
    nlinarith only [mul_le_mul_of_nonneg_left halg (hgp x).le]
  have hi := integral_mono hiP ((hiF.const_mul 2).add (hiv.const_mul (2*M))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hiF.const_mul 2) (hiv.const_mul (2*M)),integral_const_mul,integral_const_mul] at hi
  have he := real_carleman_estimate gamma phi v B hg hgp hB hs hphi hv hc a b C s t
    hC ht hlarge hquad hweight herror
  have hv0 : 0 ≤ ∫ x, gamma x*v x^2 := integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
  have habsm := mul_le_mul_of_nonneg_right habs hv0
  change _ ≤ ∫ x, gamma x*(P x+potential x*v x)^2
  change _ ≤ ∫ x, gamma x*(P x)^2 at he
  nlinarith only [he,hi,habsm]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCarlemanLocalConditions
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix Metric
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma realTransportBilinear_diagonal (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord) (x xi : Yau.Jets.Coord) :
    realTransportBilinear B V x xi xi = realTransportQuadratic B V x xi := by
  simp [realTransportBilinear,realTransportQuadratic,mul_assoc]

lemma realTransportBilinear_continuous (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) : Continuous (realTransportBilinear B V) := by
  apply continuous_finsetSum; intro i _
  apply continuous_finsetSum; intro j _
  apply continuous_finsetSum; intro k _
  exact ((((continuous_const.mul (hB i j).continuous).mul
    (Yau.real_coordPartial_smooth _ (hV k) i).continuous).smul continuous_const)).sub
    (((hV k).continuous.mul (Yau.real_coordPartial_smooth _ (hB i j) k).continuous).smul continuous_const)

theorem real_carleman_local_conditions (gamma q : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0) (hq : ContDiff ℝ ∞ q)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (x0 : Yau.Jets.Coord) (s : ℝ)
    (hquad : ∀ xi : Yau.Jets.Coord, xi ≠ 0 →
      0 < realTransportQuadratic B V x0 xi+s*coordMatrixForm (B x0) xi xi)
    (hweight : 0 < Yau.pairing q V x0-s*q x0) :
    ∃ r > 0, ∃ a > 0, ∃ b > 0, ∃ C > 0, ∀ x ∈ ball x0 r,
      (∀ xi : Yau.Jets.Coord, a*(∑ i, (xi i)^2) ≤
        realTransportQuadratic B V x xi+s*coordMatrixForm (B x) xi xi) ∧
      b ≤ Yau.pairing q V x-s*q x ∧
      realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x ≤ C := by
  let g := fun x ↦ realTransportBilinear B V x+s • coordMatrixForm (B x)
  have hgc : Continuous g := (realTransportBilinear_continuous B V hB hV).add
    ((coordMatrixForm_continuous B (fun i j ↦ (hB i j).continuous)).const_smul s)
  have hgp (xi : Yau.Jets.Coord) (hxi : xi ≠ 0) : 0 < g x0 xi xi := by
    simpa only [g,_root_.add_apply,_root_.smul_apply,smul_eq_mul,realTransportBilinear_diagonal] using hquad xi hxi
  obtain ⟨r0,hr0,a,ha,hqa⟩ := local_bilinear_coercivity g hgc x0 hgp
  let F := fun x ↦ Yau.pairing q V x-s*q x
  have hF : Continuous F := (Yau.pairing_smooth hq hV).continuous.sub (continuous_const.mul hq.continuous)
  have ho : IsOpen {x | F x0/2 < F x} := isOpen_lt continuous_const hF
  obtain ⟨r1,hr1,hrF⟩ := Metric.isOpen_iff.mp ho x0 (by change F x0/2 < F x0; dsimp [F]; linarith only [hweight])
  let r := min r0 r1
  have hr : 0 < r := lt_min hr0 hr1
  have hR := realWeightedElliptic_smooth gamma B (Yau.weightedDiv gamma V) hg hgn hB
    (Yau.weightedDiv_smooth hg hgn hV)
  obtain ⟨C,hC,hCB⟩ := ((isCompact_closedBall x0 r).image hR.continuous).isBounded.exists_pos_norm_le
  refine ⟨r,hr,a,ha,F x0/2,by dsimp [F] <;> positivity,C,hC,?_⟩
  intro x hx
  have hx0 : x ∈ ball x0 r0 := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _))
  have hx1 : x ∈ ball x0 r1 := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hx) (min_le_right _ _))
  refine ⟨?_,(hrF hx1).le,?_⟩
  · intro xi
    simpa only [g,_root_.add_apply,_root_.smul_apply,smul_eq_mul,realTransportBilinear_diagonal] using hqa x hx0 xi
  · exact (le_abs_self _).trans (hCB _ ⟨x,mem_closedBall.mpr (le_of_lt (mem_ball.mp hx)),rfl⟩)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealConvexifiedPhase
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

lemma realConvexifiedPhase_smooth (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ) :
    ContDiff ℝ ∞ (realConvexifiedPhase psi K) := hpsi.add (contDiff_const.mul (hpsi.pow 2))

lemma realConvexifiedPhase_partial (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (K : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (realConvexifiedPhase psi K) x i = (1+2*K*psi x)*Yau.coordPartial psi x i := by
  have he : realConvexifiedPhase psi K = fun y ↦ psi y+K*(psi y*psi y) := by funext y; simp [realConvexifiedPhase,pow_two]
  rw [he,Yau.real_coordPartial_add _ _ hpsi (contDiff_const.mul (hpsi.mul hpsi)),
    Yau.real_coordPartial_const_mul _ (hpsi.mul hpsi),Yau.real_coordPartial_mul _ _ hpsi hpsi]
  ring

lemma realConvexifiedPhase_factor_partial (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (K : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (fun y ↦ 1+2*K*psi y) x i = 2*K*Yau.coordPartial psi x i := by
  rw [Yau.real_coordPartial_add _ _ contDiff_const (contDiff_const.mul hpsi),
    Yau.real_coordPartial_const_mul psi hpsi]
  simp [Yau.coordPartial]

lemma realMatrixFlux_convexified (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    realMatrixFlux B (realConvexifiedPhase psi K) x i = (1+2*K*psi x)*realMatrixFlux B psi x i := by
  simp only [realMatrixFlux,realConvexifiedPhase_partial psi hpsi,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; ring

lemma realMatrixEnergy_convexified (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K) x =
      (1+2*K*psi x)^2*realMatrixEnergy B psi psi x := by
  simp only [realMatrixEnergy_apply,realConvexifiedPhase_partial psi hpsi,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

lemma realMatrixFlux_convexified_derivative (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ)
    (x : Yau.Jets.Coord) (hx : psi x = 0) (i k : Fin 4) :
    Yau.coordPartial (fun y ↦ realMatrixFlux B (realConvexifiedPhase psi K) y k) x i =
      Yau.coordPartial (fun y ↦ realMatrixFlux B psi y k) x i +
      2*K*Yau.coordPartial psi x i*realMatrixFlux B psi x k := by
  have he : (fun y ↦ realMatrixFlux B (realConvexifiedPhase psi K) y k) =
      (fun y ↦ (1+2*K*psi y)*realMatrixFlux B psi y k) :=
    funext (fun y ↦ realMatrixFlux_convexified B psi hpsi K y k)
  rw [he,Yau.real_coordPartial_mul _ _ (contDiff_const.add (contDiff_const.mul hpsi))
    (realMatrixFlux_smooth B psi hB hpsi k),realConvexifiedPhase_factor_partial psi hpsi,hx]
  ring

lemma realMatrixEnergy_convexified_derivative (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ)
    (x : Yau.Jets.Coord) (hx : psi x = 0) (i : Fin 4) :
    Yau.coordPartial (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K)) x i =
      Yau.coordPartial (realMatrixEnergy B psi psi) x i +
      4*K*realMatrixEnergy B psi psi x*Yau.coordPartial psi x i := by
  have he : realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K) =
      fun y ↦ ((1+2*K*psi y)*(1+2*K*psi y))*realMatrixEnergy B psi psi y := by
    funext y; rw [realMatrixEnergy_convexified B psi hpsi]; ring
  have hF : ContDiff ℝ ∞ (fun y ↦ 1+2*K*psi y) := contDiff_const.add (contDiff_const.mul hpsi)
  rw [he,Yau.real_coordPartial_mul _ _ (hF.mul hF) (realMatrixEnergy_smooth B hB psi psi hpsi hpsi),
    Yau.real_coordPartial_mul _ _ hF hF,realConvexifiedPhase_factor_partial psi hpsi,hx]
  ring

theorem real_convexified_cubic (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ)
    (x : Yau.Jets.Coord) (hx : psi x = 0) :
    Yau.pairing (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K))
        (realMatrixFlux B (realConvexifiedPhase psi K)) x =
      Yau.pairing (realMatrixEnergy B psi psi) (realMatrixFlux B psi) x +
      4*K*(realMatrixEnergy B psi psi x)^2 := by
  simp only [Yau.pairing,realMatrixFlux_convexified B psi hpsi,
    realMatrixEnergy_convexified_derivative B hB psi hpsi K x hx,hx,mul_zero,add_zero,one_mul,
    add_mul,Finset.sum_add_distrib]
  have he : (∑ i, 4*K*realMatrixEnergy B psi psi x*Yau.coordPartial psi x i*realMatrixFlux B psi x i) =
      4*K*realMatrixEnergy B psi psi x*Yau.pairing psi (realMatrixFlux B psi) x := by
    simp only [Yau.pairing,Finset.mul_sum,mul_assoc]
  rw [he,realMatrixEnergy_pairing]
  ring

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealConvexifiedQuadraticLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Matrix
open scoped ContDiff

lemma real_flux_rank_one (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀ x i j, B x i j = B x j i) (psi : Yau.Jets.Coord → ℝ)
    (x xi : Yau.Jets.Coord) :
    (∑ i, ∑ j, ∑ k, B x i j*Yau.coordPartial psi x i*realMatrixFlux B psi x k*xi k*xi j) =
      (∑ k, realMatrixFlux B psi x k*xi k)^2 := by
  have hf : (∑ i, ∑ j, B x i j*Yau.coordPartial psi x i*xi j) =
      (∑ j, realMatrixFlux B psi x j*xi j) := by
    rw [Finset.sum_comm]
    simp only [realMatrixFlux,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    rw [hs x i j]
  calc
    _ = (∑ i, ∑ j, B x i j*Yau.coordPartial psi x i*xi j)*
        (∑ k, realMatrixFlux B psi x k*xi k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    _ = _ := by rw [hf,pow_two]

theorem real_convexified_quadratic (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ)
    (x : Yau.Jets.Coord) (hx : psi x = 0) (xi : Yau.Jets.Coord) :
    realTransportQuadratic B (realMatrixFlux B (realConvexifiedPhase psi K)) x xi =
      realTransportQuadratic B (realMatrixFlux B psi) x xi +
      4*K*(∑ k, realMatrixFlux B psi x k*xi k)^2 := by
  rw [← real_flux_rank_one B hs psi x xi]
  simp only [realTransportQuadratic]
  simp_rw [realMatrixFlux_convexified_derivative B hB psi hpsi K x hx]
  simp only [realMatrixFlux_convexified B psi hpsi,hx,mul_zero,add_zero,one_mul,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _; ring

open Metric

lemma realCoordinateSquare_smooth (x0 : Yau.Jets.Coord) :
    ContDiff ℝ ∞ (realCoordinateSquare x0) :=
  ContDiff.sum (fun i _ ↦ ((contDiff_apply ℝ ℝ i).sub contDiff_const).pow 2)

lemma realCoordinateSquare_zero (x0 : Yau.Jets.Coord) : realCoordinateSquare x0 x0 = 0 := by
  simp [realCoordinateSquare]

lemma realCoordinateSquare_norm (x0 x : Yau.Jets.Coord) : ‖x-x0‖^2 ≤ realCoordinateSquare x0 x :=
  coord_norm_sq_le_sum_sq (x-x0)

lemma realCoordinateSquare_partial_center (x0 : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (realCoordinateSquare x0) x0 i = 0 := by
  have hf (j : Fin 4) : ContDiff ℝ ∞ (fun x : Yau.Jets.Coord ↦ x j-x0 j) :=
    (contDiff_apply ℝ ℝ j).sub contDiff_const
  have he : realCoordinateSquare x0 = fun x ↦ ∑ j, (x j-x0 j)*(x j-x0 j) := by
    funext x; simp [realCoordinateSquare,pow_two]
  rw [he,Yau.real_coordPartial_sum _ (fun j ↦ (hf j).mul (hf j))]
  apply Finset.sum_eq_zero
  intro j _
  rw [Yau.real_coordPartial_mul _ _ (hf j) (hf j)]
  simp

lemma realIndentedPhase_smooth (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (x0 : Yau.Jets.Coord) : ContDiff ℝ ∞ (realIndentedPhase psi x0) :=
  hpsi.sub (realCoordinateSquare_smooth x0)

lemma realIndentedPhase_center (psi : Yau.Jets.Coord → ℝ) (x0 : Yau.Jets.Coord) :
    realIndentedPhase psi x0 x0 = psi x0 := by simp [realIndentedPhase,realCoordinateSquare_zero]

lemma realIndentedPhase_gradient_center (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (x0 : Yau.Jets.Coord) : realCoordGradient (realIndentedPhase psi x0) x0 = realCoordGradient psi x0 := by
  ext i
  simp only [realCoordGradient]
  unfold Yau.coordPartial realIndentedPhase
  rw [fderiv_fun_sub (hpsi.differentiable (by simp) x0)
    ((realCoordinateSquare_smooth x0).differentiable (by simp) x0)]
  have hh := realCoordinateSquare_partial_center x0 i
  simp only [Yau.coordPartial] at hh
  simp only [_root_.sub_apply,hh,sub_zero]

lemma realIndentedPhase_annulus (psi : Yau.Jets.Coord → ℝ) (x0 x : Yau.Jets.Coord)
    (s : ℝ) (hs : 0 ≤ s) (hd : s ≤ dist x x0) (hpsi : psi x ≤ 0) :
    realIndentedPhase psi x0 x ≤ -s^2 := by
  have hn := realCoordinateSquare_norm x0 x
  rw [dist_eq_norm] at hd
  have hsq : s^2 ≤ ‖x-x0‖^2 := by nlinarith only [hs,hd,norm_nonneg (x-x0)]
  dsimp [realIndentedPhase]
  linarith

lemma realConvexifiedPhase_negative_bound (psi : Yau.Jets.Coord → ℝ) (K : ℝ) (hK : 0 < K)
    (x : Yau.Jets.Coord) (hlow : -(1/(2*K)) < psi x) (hhigh : psi x ≤ 0) :
    realConvexifiedPhase psi K x ≤ psi x/2 := by
  have hk2 : 0 < 2*K := by positivity
  have hmul : -(1:ℝ) < (2*K)*psi x := by
    have hh := (div_lt_iff₀ hk2).mp (show (-1)/(2*K) < psi x by simpa only [neg_div] using hlow)
    linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1/2+K*psi x) hhigh
  dsimp [realConvexifiedPhase]
  nlinarith only [hp]

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCarlemanWeight
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem positive_bilinear_shift
    (G D : Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ)
    (hp : ∀ xi : Yau.Jets.Coord, xi ≠ 0 → 0 < G xi xi) :
    ∃ s > 0, ∀ xi : Yau.Jets.Coord, xi ≠ 0 → 0 < D xi xi+s*G xi xi := by
  obtain ⟨c,hc,C,hC,hbase⟩ := uniform_metric_coercivity (fun _ : Unit ↦ G) continuous_const (fun _ ↦ hp)
  let s := (‖D‖+1)/c
  have hs : 0 < s := by dsimp [s] <;> positivity
  have hsc : s*c = ‖D‖+1 := by dsimp [s]; field_simp
  refine ⟨s,hs,?_⟩
  intro xi hxi
  have hD : |D xi xi| ≤ ‖D‖*‖xi‖^2 := by
    simpa only [pow_two,mul_assoc] using bilinear_pairing_bound D xi xi
  have hG := mul_le_mul_of_nonneg_left ((hbase ()).2 xi) hs.le
  change s*(c*‖xi‖^2) ≤ s*G xi xi at hG
  rw [← mul_assoc,hsc] at hG
  have hlo := (abs_le.mp hD).1
  have hn : 0 < ‖xi‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hxi)
  nlinarith only [hG,hlo,hn]

theorem real_carleman_weight_at_point
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (x0 : Yau.Jets.Coord) (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0)
    (hpos : (B x0).PosDef) :
    ∃ K > 0, ∃ s > 0,
      (∀ xi : Yau.Jets.Coord, xi ≠ 0 →
        0 < realTransportQuadratic B (realMatrixFlux B (realConvexifiedPhase psi K)) x0 xi +
          s*coordMatrixForm (B x0) xi xi) ∧
      0 < Yau.pairing (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K))
        (realMatrixFlux B (realConvexifiedPhase psi K)) x0 -
        s*realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K) x0 := by
  obtain ⟨s,hs,hshift⟩ := positive_bilinear_shift (coordMatrixForm (B x0))
    (realTransportBilinear B (realMatrixFlux B psi) x0) (coordMatrixForm_positive (B x0) hpos)
  let q := realMatrixEnergy B psi psi x0
  let P := Yau.pairing (realMatrixEnergy B psi psi) (realMatrixFlux B psi) x0
  have hq : 0 < q := coordMatrixForm_positive (B x0) hpos _ hgrad
  let K := (|P-s*q|+1)/(4*q^2)
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hKq : 4*K*q^2 = |P-s*q|+1 := by dsimp [K]; field_simp
  refine ⟨K,hK,s,hs,?_,?_⟩
  · intro xi hxi
    rw [real_convexified_quadratic B hB hsym psi hpsi K x0 hzero]
    have hh := hshift xi hxi
    rw [realTransportBilinear_diagonal] at hh
    have hnon := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hK.le)
      (sq_nonneg (∑ k, realMatrixFlux B psi x0 k*xi k))
    linarith only [hh,hnon]
  · rw [real_convexified_cubic B hB psi hpsi K x0 hzero,realMatrixEnergy_convexified B psi hpsi,
      hzero,mul_zero,add_zero,one_pow,one_mul]
    change 0 < P+4*K*q^2-s*q
    rw [hKq]
    have hh := neg_abs_le (P-s*q)
    linarith only [hh]

theorem real_carleman_weight_on_ball (gamma : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (x0 : Yau.Jets.Coord) (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0)
    (hpos : (B x0).PosDef) :
    ∃ K > 0, ∃ s > 0, ∃ r > 0, ∃ a > 0, ∃ b > 0, ∃ C > 0,
      ∀ x ∈ Metric.ball x0 r,
        (∀ xi : Yau.Jets.Coord, a*(∑ i, (xi i)^2) ≤
          realTransportQuadratic B (realMatrixFlux B (realConvexifiedPhase psi K)) x xi +
          s*coordMatrixForm (B x) xi xi) ∧
        b ≤ Yau.pairing (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K))
          (realMatrixFlux B (realConvexifiedPhase psi K)) x -
          s*realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K) x ∧
        realWeightedElliptic gamma B (realWeightedElliptic gamma B (realConvexifiedPhase psi K)) x ≤ C := by
  obtain ⟨K,hK,s,hs,hQ,hW⟩ := real_carleman_weight_at_point B hB hsym psi hpsi x0 hzero hgrad hpos
  have hphi := realConvexifiedPhase_smooth psi hpsi K
  obtain ⟨r,hr,a,ha,b,hb,C,hC,hlocal⟩ := real_carleman_local_conditions gamma
    (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K)) B
    (realMatrixFlux B (realConvexifiedPhase psi K)) hg hgn
    (realMatrixEnergy_smooth B hB _ _ hphi hphi) hB (realMatrixFlux_smooth B _ hB hphi) x0 s hQ hW
  exact ⟨K,hK,s,hs,r,hr,a,ha,b,hb,C,hC,hlocal⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealLocalCarleman
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix Metric MeasureTheory
open scoped ContDiff
noncomputable section

theorem real_local_carleman (gamma potential psi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hpsi : ContDiff ℝ ∞ psi) (x0 : Yau.Jets.Coord)
    (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0) (hpos : (B x0).PosDef) :
    ∃ K > 0, ∃ r > 0, ∃ a > 0, ∃ b > 0, ∃ T > 0,
      let phi := realConvexifiedPhase psi K
      ∀ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
        tsupport v ⊆ ball x0 r → ∀ t : ℝ, T ≤ t →
          a*t*(∫ x, gamma x*realGradientSquare v x) + (b*t^3/4)*(∫ x, gamma x*v x^2) ≤
            (∫ x, gamma x*(Real.exp (t*phi x)*
              (realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x +
                potential x*(Real.exp (-t*phi x)*v x)))^2) := by
  obtain ⟨K,hK,s,hs,r,hr,a,ha,b,hb,C,hC,hlocal⟩ := real_carleman_weight_on_ball gamma hg
    (fun x ↦ (hgp x).ne') B hB hsym psi hpsi x0 hzero hgrad hpos
  let phi := realConvexifiedPhase psi K
  have hphi : ContDiff ℝ ∞ phi := realConvexifiedPhase_smooth psi hpsi K
  obtain ⟨M,hM,hMb⟩ := ((isCompact_closedBall x0 r).image hpot.continuous).isBounded.exists_pos_norm_le
  let T := max 1 ((C+s^2+4*M^2)/b)
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K,hK,r,hr,a,ha,b,hb,T,hT,?_⟩
  dsimp only
  intro v hv hc hvs t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht1
  have hbig : C+s^2+4*M^2 ≤ b*t := by
    have hh := (div_le_iff₀ hb).mp ((le_max_right _ _).trans ht)
    simpa only [mul_comm] using hh
  have hlarge : C+s^2 ≤ b*t := by nlinarith only [hbig,sq_nonneg M]
  have habs : 4*M^2 ≤ b*t^3 := by
    have hx := mul_nonneg hb.le (mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1))
      (show 0 ≤ t+1 by positivity))
    nlinarith only [hbig,hx,sq_nonneg s,hC.le]
  have hpotB (x : Yau.Jets.Coord) (hx : x ∈ tsupport v) : (potential x)^2 ≤ M^2 := by
    have hbnd : |potential x| ≤ M := hMb _ ⟨x,mem_closedBall.mpr (mem_ball.mp (hvs hx)).le,rfl⟩
    nlinarith only [hbnd,abs_nonneg (potential x),hM.le,sq_abs (potential x)]
  have he := real_carleman_potential_estimate gamma phi v B hg hgp hB hsym hphi hv hc a b C s t
    hC.le ht1 hlarge (fun x hx ↦ (hlocal x (hvs hx)).1)
    (fun x hx ↦ (hlocal x (hvs hx)).2.1) (fun x hx ↦ (hlocal x (hvs hx)).2.2)
    potential hpot (M^2) hpotB habs
  have hexp (x : Yau.Jets.Coord) : Real.exp (t*phi x)*Real.exp (-t*phi x) = 1 := by
    rw [← Real.exp_add,show t*phi x + -t*phi x = 0 by ring,Real.exp_zero]
  have hid (x : Yau.Jets.Coord) : Real.exp (t*phi x)*
      (realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x +
        potential x*(Real.exp (-t*phi x)*v x)) =
      Real.exp (t*phi x)*realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x +
        potential x*v x := by
    linear_combination potential x*v x*hexp x
  change _ ≤ ∫ x, gamma x*(Real.exp (t*phi x)*
    (realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x +
      potential x*(Real.exp (-t*phi x)*v x)))^2
  simp_rw [hid]
  exact he

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCarlemanSupport
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open MeasureTheory Metric
open scoped ContDiff
noncomputable section

lemma real_carleman_weighted_mass (gamma potential phi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hgp : ∀ x, 0 < gamma x) (hphi : ContDiff ℝ ∞ phi)
    (x0 : Yau.Jets.Coord) (r a b T : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hcar : ∀ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ ball x0 r → ∀ t : ℝ, T ≤ t →
      a*t*(∫ x, gamma x*realGradientSquare v x)+(b*t^3/4)*(∫ x, gamma x*v x^2) ≤
      (∫ x, gamma x*(Real.exp (t*phi x)*
        realEllipticResidual gamma potential B (fun y ↦ Real.exp (-t*phi y)*v y) x)^2))
    (f : Yau.Jets.Coord → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ ball x0 r) (t : ℝ) (ht : max T 1 ≤ t) :
    (∫ x, Real.exp ((2*t)*phi x)*((b/4)*gamma x*f x^2)) ≤
      (∫ x, Real.exp ((2*t)*phi x)*(gamma x*(realEllipticResidual gamma potential B f x)^2)) := by
  let v := fun x ↦ Real.exp (t*phi x)*f x
  have hv : ContDiff ℝ ∞ v := (contDiff_const.mul hphi).exp.mul hf
  have hvc : HasCompactSupport v := hc.mul_left
  have hvs : tsupport v ⊆ ball x0 r := tsupport_mul_subset_right.trans hs
  have hinv : (fun y ↦ Real.exp (-t*phi y)*v y) = f := by
    funext y
    dsimp [v]
    rw [← mul_assoc,← Real.exp_add,show -t*phi y+t*phi y=0 by ring,Real.exp_zero,one_mul]
  have hh := hcar v hv hvc hvs t ((le_max_left _ _).trans ht)
  rw [hinv] at hh
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hg0 : 0 ≤ a*t*(∫ x, gamma x*realGradientSquare v x) :=
    mul_nonneg (mul_nonneg ha.le ht0) (integral_nonneg (fun x ↦
      mul_nonneg (hgp x).le (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))))
  have hv0 : 0 ≤ ∫ x, gamma x*v x^2 := integral_nonneg (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
  have ht3 : 1 ≤ t^3 := one_le_pow₀ ht1
  have hcub := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht3 (by positivity : 0 ≤ b/4)) hv0
  have he (x : Yau.Jets.Coord) : (Real.exp (t*phi x))^2 = Real.exp ((2*t)*phi x) := by
    rw [pow_two,← Real.exp_add]; congr 1; ring
  have hleft : (∫ x, Real.exp ((2*t)*phi x)*((b/4)*gamma x*f x^2)) =
      (b/4)*(∫ x, gamma x*v x^2) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [v]
    rw [mul_pow,he]; ring
  have hright : (∫ x, Real.exp ((2*t)*phi x)*(gamma x*(realEllipticResidual gamma potential B f x)^2)) =
      (∫ x, gamma x*(Real.exp (t*phi x)*realEllipticResidual gamma potential B f x)^2) := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [mul_pow,he]; ring
  rw [hleft,hright]
  nlinarith only [hh,hg0,hcub]

theorem real_local_carleman_support (gamma potential psi : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hpsi : ContDiff ℝ ∞ psi) (x0 : Yau.Jets.Coord)
    (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0) (hpos : (B x0).PosDef) :
    ∃ K > 0, ∃ r > 0, ∀ f : Yau.Jets.Coord → ℝ,
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ ball x0 r →
      ∀ c : ℝ, (∀ x, realEllipticResidual gamma potential B f x ≠ 0 →
        realConvexifiedPhase psi K x ≤ c) →
      ∀ y, c < realConvexifiedPhase psi K y → f y = 0 := by
  obtain ⟨K,hK,r,hr,a,ha,b,hb,T,hT,hcar⟩ :=
    real_local_carleman gamma potential psi B hg hgp hpot hB hsym hpsi x0 hzero hgrad hpos
  let phi := realConvexifiedPhase psi K
  have hphi : ContDiff ℝ ∞ phi := realConvexifiedPhase_smooth psi hpsi K
  refine ⟨K,hK,r,hr,?_⟩
  intro f hf hc hs c hgap y hy
  let F := fun x ↦ (b/4)*gamma x*f x^2
  let G := fun x ↦ gamma x*(realEllipticResidual gamma potential B f x)^2
  have hR := realEllipticResidual_smooth gamma potential B f hg (fun x ↦ (hgp x).ne') hpot hB hf
  have hcR := realEllipticResidual_compact gamma potential B f hc
  have hF : Continuous F := ((continuous_const.mul hg.continuous).mul (hf.continuous.pow 2))
  have hG : Continuous G := hg.continuous.mul (hR.continuous.pow 2)
  have hcf2 : HasCompactSupport (fun x ↦ f x^2) := by
    convert hc.mul_right (f' := f) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext point; simp [pow_two])
  have hcr2 : HasCompactSupport (fun x ↦ (realEllipticResidual gamma potential B f x)^2) := by
    convert hcR.mul_right (f' := realEllipticResidual gamma potential B f) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (ext point; simp [pow_two])
  have hbound (t : ℝ) (ht : max T 1 ≤ t) :
      (∫ x, Real.exp (t*(2*phi x))*F x) ≤ (∫ x, Real.exp (t*(2*phi x))*G x) := by
    have hh := real_carleman_weighted_mass gamma potential phi B hgp hphi x0 r a b T ha hb
      hcar f hf hc hs t ht
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> funext x <;> dsimp [F,G] <;> congr 2 <;> ring)
  have hsep := exponential_integral_separation F G (fun x ↦ 2*phi x) hF hG
    (continuous_const.mul hphi.continuous) hcf2.mul_left hcr2.mul_left
    (fun x ↦ mul_nonneg (mul_nonneg (by positivity) (hgp x).le) (sq_nonneg _))
    (fun x ↦ mul_nonneg (hgp x).le (sq_nonneg _))
    (2*c) (max T 1) (fun x hx ↦ by
      have hn : realEllipticResidual gamma potential B f x ≠ 0 := by
        intro hz; apply hx; simp [G,hz]
      exact mul_le_mul_of_nonneg_left (hgap x hn) (by norm_num)) hbound y
    (mul_lt_mul_of_pos_left hy (by norm_num))
  dsimp [F] at hsep
  have hbf : (b/4)*gamma y ≠ 0 := mul_ne_zero (div_ne_zero hb.ne' (by norm_num)) (hgp y).ne'
  exact sq_eq_zero_iff.mp (mul_eq_zero.mp hsep |>.resolve_left hbf)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealOneSidedPropagation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Metric Filter
open scoped ContDiff Topology
noncomputable section

theorem real_one_sided_strict_zero_propagation (gamma potential psi W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hpsi : ContDiff ℝ ∞ psi) (hW : ContDiff ℝ ∞ W)
    (x0 : Yau.Jets.Coord) (R : ℝ) (hR : 0 < R)
    (hzero : psi x0 = 0) (hgrad : realCoordGradient psi x0 ≠ 0) (hpos : (B x0).PosDef)
    (hEq : ∀ x ∈ ball x0 R, realEllipticResidual gamma potential B W x = 0)
    (hside : ∀ x ∈ ball x0 R, 0 < psi x → W x = 0) :
    ∃ eps > 0, eps ≤ R ∧ ∀ x ∈ ball x0 eps, W x = 0 := by
  let psi0 := realIndentedPhase psi x0
  have hpsi0 : ContDiff ℝ ∞ psi0 := realIndentedPhase_smooth psi hpsi x0
  have hz0 : psi0 x0 = 0 := (realIndentedPhase_center psi x0).trans hzero
  have hg0 : realCoordGradient psi0 x0 ≠ 0 := by
    rw [realIndentedPhase_gradient_center psi hpsi]; exact hgrad
  obtain ⟨K,hK,r,hr,hcar⟩ := real_local_carleman_support gamma potential psi0 B hg hgp hpot
    hB hsym hpsi0 x0 hz0 hg0 hpos
  let phi := realConvexifiedPhase psi0 K
  have hphi : ContDiff ℝ ∞ phi := realConvexifiedPhase_smooth psi0 hpsi0 K
  have hphiz : phi x0 = 0 := by simp [phi,realConvexifiedPhase,hz0]
  have hlow0 : -(1/(2*K)) < psi0 x0 := by rw [hz0]; exact neg_neg_of_pos (by positivity)
  obtain ⟨r0,hr0,hnear⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const hpsi0.continuous) x0 hlow0
  let s := min R (min r r0)/4
  have hs : 0 < s := by dsimp [s] <;> positivity
  have hsR : 2*s < R := by
    have hh := min_le_left R (min r r0); dsimp [s] <;> linarith
  have hsr : 2*s < r := by
    have hh := (min_le_right R (min r r0)).trans (min_le_left r r0); dsimp [s] <;> linarith
  have hsr0 : 2*s < r0 := by
    have hh := (min_le_right R (min r r0)).trans (min_le_right r r0); dsimp [s] <;> linarith
  obtain ⟨eta,heta,hetac,hetas,hetar,heta1⟩ := compact_smooth_cutoff
    (isCompact_closedBall x0 s) isOpen_ball
    (closedBall_subset_ball (by linarith : s < 2*s))
  let f := fun x ↦ eta x*W x
  have hf : ContDiff ℝ ∞ f := heta.mul hW
  have hfc : HasCompactSupport f := hetac.mul_right
  have hfs : tsupport f ⊆ ball x0 r :=
    tsupport_mul_subset_left.trans (hetas.trans (ball_subset_ball hsr.le))
  have hres (x) (hx : realEllipticResidual gamma potential B f x ≠ 0) : phi x ≤ -s^2/2 := by
    have hxeta : x ∈ tsupport eta := tsupport_mul_subset_left
      (realEllipticResidual_tsupport gamma potential B f (subset_tsupport _ hx))
    have hx2 := hetas hxeta
    obtain ⟨hxR,hd,hps⟩ := real_cutoff_residual_location gamma potential eta W psi B hpsi.continuous
      x0 R s (hetas.trans (ball_subset_ball hsR.le)) heta1 hEq hside x hx
    have hupper : psi0 x ≤ -s^2 := realIndentedPhase_annulus psi x0 x s hs.le hd hps
    have hlower : -(1/(2*K)) < psi0 x := hnear (ball_subset_ball hsr0.le hx2)
    have hh := realConvexifiedPhase_negative_bound psi0 K hK x hlower
      (hupper.trans (neg_nonpos.mpr (sq_nonneg s)))
    change phi x ≤ _ at hh
    linarith
  have hneg : -s^2/2 < phi x0 := by rw [hphiz]; nlinarith [sq_pos_of_pos hs]
  obtain ⟨eps0,heps0,heps⟩ := Metric.isOpen_iff.mp
    (isOpen_lt continuous_const hphi.continuous) x0 hneg
  let eps := min s eps0
  have hepspos : 0 < eps := lt_min hs heps0
  refine ⟨eps,hepspos,?_,?_⟩
  · exact (min_le_left _ _).trans (by linarith)
  · intro x hx
    have hxphi : -s^2/2 < phi x := heps (ball_subset_ball (min_le_right _ _) hx)
    have hfx : f x = 0 := hcar f hf hfc hfs (-s^2/2) hres x hxphi
    have hxclosed : x ∈ closedBall x0 s := mem_closedBall.mpr
      ((mem_ball.mp hx).le.trans (min_le_left _ _))
    have he := (heta1 x hxclosed).self_of_nhds
    simpa only [f,he,one_mul] using hfx

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSphericalPhase
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

lemma realCoordinateSquare_partial (y x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (realCoordinateSquare y) x i = 2*(x i-y i) := by
  have hf (j : Fin 4) : ContDiff ℝ ∞ (fun z : Yau.Jets.Coord ↦ z j-y j) :=
    (contDiff_apply ℝ ℝ j).sub contDiff_const
  have hp (j : Fin 4) : Yau.coordPartial (fun z : Yau.Jets.Coord ↦ z j-y j) x i = (Pi.single i (1:ℝ) : Yau.Jets.Coord) j := by
    have hh := ((ContinuousLinearMap.proj j : Yau.Jets.Coord →L[ℝ] ℝ).hasFDerivAt (x := x) |>.sub_const (y j)).fderiv
    change fderiv ℝ (fun z : Yau.Jets.Coord ↦ z j-y j) x = ContinuousLinearMap.proj j at hh
    unfold Yau.coordPartial
    rw [hh]
    rfl
  have he : realCoordinateSquare y = fun z ↦ ∑ j, (z j-y j)*(z j-y j) := by
    funext z; simp [realCoordinateSquare,pow_two]
  rw [he,Yau.real_coordPartial_sum _ (fun j ↦ (hf j).mul (hf j))]
  simp_rw [Yau.real_coordPartial_mul _ _ (hf _) (hf _),hp]
  rw [Finset.sum_eq_single i]
  · simp <;> ring
  · intro j _ hji; simp [hji]
  · simp

lemma realSphericalPhase_gradient (y x : Yau.Jets.Coord) (c : ℝ) :
    realCoordGradient (fun z ↦ c-realCoordinateSquare y z) x = fun i ↦ -2*(x i-y i) := by
  ext i
  unfold realCoordGradient Yau.coordPartial
  rw [fderiv_fun_sub (differentiableAt_const c) ((realCoordinateSquare_smooth y).differentiable (by simp) x)]
  simp only [fderiv_fun_const,Pi.zero_apply,zero_sub]
  have hh := realCoordinateSquare_partial y x i
  simp only [Yau.coordPartial] at hh
  change -(fderiv ℝ (realCoordinateSquare y) x (Pi.single i 1)) = _
  rw [hh]
  ring

lemma realSphericalPhase_gradient_ne_zero (y x : Yau.Jets.Coord) (c : ℝ) (hx : x ≠ y) :
    realCoordGradient (fun z ↦ c-realCoordinateSquare y z) x ≠ 0 := by
  rw [realSphericalPhase_gradient]
  intro hh
  apply hx
  ext i
  have hi := congrFun hh i
  change -2*(x i-y i)=0 at hi
  linarith

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealZeroBallExpansion
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Metric Filter Set
open scoped ContDiff Topology
noncomputable section

theorem real_zero_germ_expands (gamma potential W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ x, (B x).PosDef)
    (y : Yau.Jets.Coord) (R : ℝ) (hR : 0 < R)
    (hEq : ∀ x ∈ ball y R, realEllipticResidual gamma potential B W x = 0)
    (hy : W =ᶠ[𝓝 y] (fun _ ↦ 0)) : ∀ x ∈ ball y (R/4), W x = 0 := by
  intro x hx
  by_contra hxW
  let C := tsupport W ∩ closedBall y R
  have hCx : x ∈ C := ⟨subset_tsupport _ hxW,mem_closedBall.mpr
    ((mem_ball.mp hx).le.trans (by linarith))⟩
  have hCc : IsCompact C := (isCompact_closedBall y R).inter_left (isClosed_tsupport W)
  obtain ⟨z,hz,hmin⟩ := hCc.exists_isMinOn ⟨x,hCx⟩ (realCoordinateSquare_smooth y).continuous.continuousOn
  have hzx : realCoordinateSquare y z ≤ realCoordinateSquare y x := hmin hCx
  have hxupper : realCoordinateSquare y x ≤ 4*dist x y^2 := by
    simpa only [realCoordinateSquare,dist_eq_norm,Pi.sub_apply] using coord_sum_sq_le_four_norm_sq (x-y)
  have hzR2 : realCoordinateSquare y z < R^2 := by
    have hd := mem_ball.mp hx
    nlinarith only [hzx,hxupper,hd,dist_nonneg (x := x) (y := y),hR]
  have hzR : dist z y < R := by
    have hn := realCoordinateSquare_norm y z
    rw [← dist_eq_norm] at hn
    nlinarith only [hn,hzR2,dist_nonneg (x := z) (y := y),hR]
  have hzy : z ≠ y := by
    intro he; subst z
    exact (notMem_tsupport_iff_eventuallyEq.mpr hy) hz.1
  let psi := fun w ↦ realCoordinateSquare y z-realCoordinateSquare y w
  have hpsi : ContDiff ℝ ∞ psi := contDiff_const.sub (realCoordinateSquare_smooth y)
  have hpsi0 : psi z = 0 := sub_self _
  have hgrad : realCoordGradient psi z ≠ 0 := realSphericalPhase_gradient_ne_zero y z _ hzy
  have hside (w : Yau.Jets.Coord) (hp : 0 < psi w) : W w = 0 := by
    by_contra hn
    have hQ : realCoordinateSquare y w < realCoordinateSquare y z := sub_pos.mp hp
    have hwR : dist w y < R := by
      have hh := realCoordinateSquare_norm y w
      rw [← dist_eq_norm] at hh
      nlinarith only [hh,hQ,hzR2,dist_nonneg (x := w) (y := y),hR]
    exact (not_le_of_gt hQ) (hmin ⟨subset_tsupport _ hn,mem_closedBall.mpr hwR.le⟩)
  let delta := R-dist z y
  have hd : 0 < delta := sub_pos.mpr hzR
  have hsub : ball z delta ⊆ ball y R := by
    intro w hw
    have hh := dist_triangle w z y
    have hw' := mem_ball.mp hw
    apply mem_ball.mpr
    dsimp [delta] at hw'
    linarith
  obtain ⟨eps,heps,_,hzero⟩ := real_one_sided_strict_zero_propagation gamma potential psi W B
    hg hgp hpot hB hsym hpsi hW z delta hd hpsi0 hgrad (hpos z)
    (fun w hw ↦ hEq w (hsub hw)) (fun w _ hp ↦ hside w hp)
  have he : W =ᶠ[𝓝 z] (fun _ ↦ 0) := by
    filter_upwards [ball_mem_nhds z heps] with w hw
    exact hzero w hw
  exact (notMem_tsupport_iff_eventuallyEq.mpr he) hz.1

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Persistence_RealWeakUniqueContinuation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Metric Filter Set
open scoped ContDiff Topology
noncomputable section

theorem real_weak_unique_continuation (gamma potential W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ x, (B x).PosDef)
    (U : Set Yau.Jets.Coord) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hEq : ∀ x ∈ U, realEllipticResidual gamma potential B W x = 0)
    (y : Yau.Jets.Coord) (hyU : y ∈ U) (hy : W =ᶠ[𝓝 y] (fun _ ↦ 0)) :
    ∀ x ∈ U, W x = 0 := by
  let Z := (tsupport W)ᶜ
  have hopen : IsOpen Z := (isClosed_tsupport W).isOpen_compl
  have hnon : (U ∩ Z).Nonempty := ⟨y,hyU,notMem_tsupport_iff_eventuallyEq.mpr hy⟩
  have hclosed : closure Z ∩ U ⊆ Z := by
    intro x hx
    obtain ⟨R,hR,hRU⟩ := Metric.isOpen_iff.mp hU x hx.2
    obtain ⟨z,hz,hxz⟩ := Metric.mem_closure_iff.mp hx.1 (R/16) (by positivity)
    have hsub : ball z (R/2) ⊆ U := by
      intro w hw
      apply hRU
      apply mem_ball.mpr
      have hh := dist_triangle w z x
      rw [dist_comm z x] at hh
      have hw' := mem_ball.mp hw
      linarith
    have hzero := real_zero_germ_expands gamma potential W B hg hgp hpot hB hsym hW hpos
      z (R/2) (by positivity) (fun w hw ↦ hEq w (hsub hw))
      (notMem_tsupport_iff_eventuallyEq.mp hz)
    have he : W =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      filter_upwards [ball_mem_nhds x (by positivity : 0 < R/16)] with w hw
      apply hzero
      apply mem_ball.mpr
      have hh := dist_triangle w x z
      have hw' := mem_ball.mp hw
      linarith
    exact notMem_tsupport_iff_eventuallyEq.mpr he
  have hall := hconn.subset_of_closure_inter_subset hopen hnon hclosed
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (hall hx)

theorem real_global_unique_continuation_oai (gamma potential W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ x, (B x).PosDef)
    (hEq : ∀ x, realEllipticResidual gamma potential B W x = 0)
    (y : Yau.Jets.Coord) (hy : W =ᶠ[𝓝 y] (fun _ ↦ 0)) : W = 0 := by
  funext x
  exact real_weak_unique_continuation gamma potential W B hg hgp hpot hB hsym hW hpos
    univ isOpen_univ isPreconnected_univ (fun x _ ↦ hEq x) y (mem_univ _) hy x (mem_univ _)

end
end Yau.Geometry

end OAI
end

theorem solution : type_of% @OAI.Yau.Geometry.real_global_unique_continuation_oai := @OAI.Yau.Geometry.real_global_unique_continuation_oai
