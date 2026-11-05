-- Prove2me | solution 1 for Viterbo.Cap.galerkin_cerami
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T17:54:38.808014+00:00
-- url     : https://prove2.me/submissions/fce84534-f85a-403e-bddd-81f352c99f4b

import Mathlib
import Definitions.Def_OAIQWSP000
import Theorems.Thm_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Definitions.Def_ViterboCap
universe u3 u4 u5 u6 u78 u79 u80 u81 u82 u83 u84 u85 u86 u87 u88 u89 u90 u91 u92 u93 u94 u95 u96 u97 u98 u99 u100 u101 u102 u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115 u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127

section
section
-- module Solutions.OAIQW_SymmetricPolar.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
end OAICompat434
end

section
-- module Solutions.OAIQW_SymmetricPolar.LocalODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

noncomputable section

theorem curve_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    EqOn (curve hV h hh x) (fun _ => x) (Icc 0 1) := by
  apply EqOn.symm
  apply curve_unique hV h hh x continuousOn_const
  · intro t _
    simpa only [hx, smul_zero] using (hasDerivWithinAt_const t (Ici t) x)
  · rfl

@[simp] theorem step_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    step hV h hh x = x := by
  have he := curve_of_eq_zero hV h hh x hx (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using he

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline
section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothDegree
noncomputable section

end
end SmoothDegree

end
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FiniteDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothLinking
noncomputable section
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type u80} {F : Type u81} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

end
end SmoothLinking

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u82} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end
end FlowDescent

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u83} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end
end FlowDescent

end
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GradientLinking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff
variable {E : Type u84} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

end
end GradientDescent

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type u85} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end
end GradientDescent

namespace FiniteLinking
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {H : Type u86} {E : Type u87} {F : Type u88} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

end
end FiniteLinking

end

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

 attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions
theorem continuous_eval {ι : Type u90} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    Continuous (eval k a) := by
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (fourier (k i)).continuous)

 theorem integral_fourier (k : ℤ) :
    (∫ t : Time, fourier k t ∂μ) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply,
    eq_comm (a := (0 : ℤ))] using h

 theorem integral_conj_fourier_mul (k l : ℤ) :
    (∫ t : Time, conj (fourier k t) * fourier l t ∂μ) = if k = l then 1 else 0 := by
  simp_rw [← fourier_neg, ← fourier_add]
  rw [integral_fourier]
  simp only [neg_add_eq_zero]

 theorem integral_conj_eval_mul {ι : Type u92} {κ : Type u93} [Fintype ι] [Fintype κ]
    (k : ι → ℤ) (l : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) :
    (∫ t : Time, conj (eval k a t) * eval l b t ∂μ) =
      ∑ i, ∑ j, if k i = l j then conj (a i) * b j else 0 := by
  classical
  have he (t : Time) : conj (eval k a t) * eval l b t =
      ∑ i, ∑ j, conj (a i)*conj (fourier (k i) t)*(b j*fourier (l j) t) := by
    change conj (∑ i, a i*fourier (k i) t) * eval l b t = _
    rw [map_sum, Finset.sum_mul]
    simp only [map_mul, eval, Finset.mul_sum]
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      simp_rw [show ∀ t : Time, conj (a i) * conj (fourier (k i) t) *
          (b j * fourier (l j) t) =
          (conj (a i)*b j) * (conj (fourier (k i) t)*fourier (l j) t) by intro t; ring]
      rw [integral_const_mul, integral_conj_fourier_mul]
      split_ifs <;> simp
    · intro j _
      exact integrable_continuous ((continuous_const.mul ((fourier (k i)).continuous.star)).mul
        (continuous_const.mul (fourier (l j)).continuous))
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact integrable_continuous ((continuous_const.mul ((fourier (k i)).continuous.star)).mul
      (continuous_const.mul (fourier (l j)).continuous))

 theorem norm_sq_re (z : ℂ) : ‖z‖^2 = (conj z*z).re := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]

 theorem integral_norm_sq {ι : Type u94} [Fintype ι] (k : ι → ℤ) (hk : Function.Injective k)
    (a : ι → ℂ) : (∫ t : Time, ‖eval k a t‖^2 ∂μ) = ∑ i, ‖a i‖^2 := by
  classical
  simp_rw [norm_sq_re]
  have hI : Integrable (fun t : Time => conj (eval k a t) * eval k a t) μ :=
    integrable_continuous ((continuous_eval k a).star.mul (continuous_eval k a))
  change (∫ t : Time, RCLike.re (conj (eval k a t)*eval k a t) ∂μ) = _
  rw [integral_re hI, integral_conj_eval_mul]
  simp only [hk.eq_iff]
  simp

end
end FourierPolynomial

namespace WeightedSchur
noncomputable section
open Finset

end
end WeightedSchur

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

 local instance instFactLtRealOfNat_solutions_1_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
 local instance instFactLtRealOfNat_solutions_2_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
theorem real_inner_eq_complex_re {α : Type u100} [Fintype α] (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) a b = RCLike.re (inner (𝕜 := ℂ) a b) := by
  simp only [PiLp.inner_apply, real_inner_eq_re_inner, map_sum]

variable {ι : Type u101} {κ : Type u102} [Fintype ι] [Fintype κ]

 theorem integral_loop_norm_sq (k : ι → ℤ) (hk : Function.Injective k) (a : Coeff ι κ) :
    (∫ t : Time, ‖loop k a t‖^2 ∂μ) = ‖a‖^2 := by
  classical
  simp_rw [EuclideanSpace.norm_sq_eq, loop_coord]
  rw [integral_finsetSum]
  · simp_rw [integral_norm_sq k hk]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
  · intro j _
    exact integrable_continuous ((continuous_eval k _).norm.pow 2)

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_3_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u106} {κ : Type u107} [Fintype ι] [Fintype κ]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_4
variable {ι : Type u108} {κ : Type u109} [Fintype ι] [Fintype κ]

 theorem fourierCoeff_eval (k : ι → ℤ) (a : ι → ℂ) (j : ℤ) :
    fourierCoeff (eval k a) j = ∑ i, if j = k i then a i else 0 := by
  classical
  simp only [fourierCoeff, eval, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have he (t : Time) : fourier (-j) t * (a i * fourier (k i) t) =
        a i*(conj (fourier j t)*fourier (k i) t) := by rw [fourier_neg]; ring
    simp_rw [he]
    rw [integral_const_mul, integral_conj_fourier_mul]
    split_ifs <;> simp only [mul_one, mul_zero]
  · intro i _
    exact integrable_continuous ((fourier (-j)).continuous.mul
      (continuous_const.mul (fourier (k i)).continuous))

 theorem project_loop (k : ι → ℤ) (hk : Function.Injective k) (a : Coeff ι κ) :
    project k (loop k a) = a := by
  classical
  ext p
  simp only [project_apply, loop_coord, fourierCoeff_eval, hk.eq_iff]
  simp

 theorem integral_fourier_mul_conj (k : ℤ) (f : C(Time, ℂ)) :
    (∫ t : Time, conj (f t) * fourier k t ∂μ) = conj (fourierCoeff f k) := by
  rw [fourierCoeff, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul, map_mul, fourier_neg, starRingEnd_self_apply]
  ring

 theorem integral_inner_loop (k : ι → ℤ) (f : C(Time, Vector κ)) (a : Coeff ι κ) :
    (∫ t : Time, inner (𝕜 := ℝ) (f t) (loop k a t) ∂μ) =
      inner (𝕜 := ℝ) (project k f) a := by
  classical
  have hstage (j : κ) :
      (∫ t : Time, conj (f t j)*eval k (fun i => a (i,j)) t ∂μ) =
        ∑ i, conj (project k f (i,j))*a (i,j) := by
    simp only [eval, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      have he (t : Time) : conj (f t j) * (a (i,j) * fourier (k i) t) =
          (conj (f t j) * fourier (k i) t) * a (i,j) := by ring
      simp_rw [he]
      rw [integral_mul_const]
      exact congrArg (fun z => z*a (i,j))
        (integral_fourier_mul_conj (k i)
          ⟨fun t => f t j, (PiLp.continuous_apply 2 _ j).comp f.continuous⟩)
    · intro i _
      exact integrable_continuous
        ((((PiLp.continuous_apply 2 _ j).comp f.continuous).star).mul
          (continuous_const.mul (fourier (k i)).continuous))
  have hcomplex : (∫ t : Time, inner (𝕜 := ℂ) (f t) (loop k a t) ∂μ) =
      inner (𝕜 := ℂ) (project k f) a := by
    change (∫ t : Time, ∑ j, loop k a t j * conj (f t j) ∂μ) =
      ∑ p : ι × κ, a p * conj (project k f p)
    simp_rw [loop_coord, mul_comm (eval k _ _)]
    rw [integral_finsetSum]
    · simp_rw [hstage]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      congr 1
      ext j
      apply Finset.sum_congr rfl
      intro i _
      ring
    · intro j _
      exact integrable_continuous
        ((((PiLp.continuous_apply 2 _ j).comp f.continuous).star).mul
          (continuous_eval k _))
  simp only [real_inner_eq_complex_re]
  rw [integral_re (integrable_continuous
    (show Continuous (fun t => inner (𝕜 := ℂ) (f t) (loop k a t)) from
      f.continuous.inner (loop k a).continuous)), hcomplex]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_5_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u110} {κ : Type u111} [Fintype ι] [Fintype κ]

 theorem project_bessel (k : ι → ℤ) (hk : Function.Injective k) (f : C(Time, Vector κ)) :
    ‖project k f‖^2 ≤ ∫ t : Time, ‖f t‖^2 ∂μ := by
  -- coordinatewise from the published scalar Bessel inequality
  -- MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal, for the
  -- orthonormal characters fourier (k i), reindexed by Fin (card ι)
  classical
  let σ := Fintype.equivFin ι
  let e : Fin (Fintype.card ι) → Time → ℂ := fun i t => fourier (k (σ.symm i)) t
  have hcf (j : κ) : Continuous (fun t => f t j) :=
    (PiLp.continuous_apply 2 _ j).comp f.continuous
  have hj (j : κ) : ∑ i, ‖project k f (i, j)‖^2 ≤ ∫ t : Time, ‖f t j‖^2 ∂μ := by
    have h := MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal μ e
      (fun i i' => integrable_continuous
        ((fourier _).continuous.mul (Complex.continuous_conj.comp (fourier _).continuous)))
      (fun i i' => by
        have h0 := integral_conj_fourier_mul (k (σ.symm i')) (k (σ.symm i))
        simp_rw [e, mul_comm (fourier (k (σ.symm i)) _)]
        rw [h0]
        simp only [hk.eq_iff, σ.symm.injective.eq_iff, eq_comm])
      (fun t => f t j) (integrable_continuous ((hcf j).norm.pow 2))
      (fun i => integrable_continuous
        ((hcf j).mul (Complex.continuous_conj.comp (fourier _).continuous)))
    have hc (i : Fin (Fintype.card ι)) :
        (∫ t : Time, f t j * conj (e i t) ∂μ) = project k f (σ.symm i, j) := by
      rw [project_apply, fourierCoeff]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [e, smul_eq_mul, fourier_neg, mul_comm]
    simp_rw [hc] at h
    rw [← σ.symm.sum_comp]
    exact h
  calc ‖project k f‖^2 = ∑ j, ∑ i, ‖project k f (i, j)‖^2 := by
        rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    _ ≤ ∑ j, ∫ t : Time, ‖f t j‖^2 ∂μ := Finset.sum_le_sum fun j _ => hj j
    _ = ∫ t : Time, ‖f t‖^2 ∂μ := by
        rw [← integral_finsetSum]
        · simp_rw [EuclideanSpace.norm_sq_eq]
        · intro j _
          exact integrable_continuous ((hcf j).norm.pow 2)

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_6
variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem hasGradientAt_potential (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) :
    HasGradientAt (potential k H) (project k (gradLoop k hH a)) a := by
  have hl : HasFDerivAt (loop k) (loopCLM k) a := by
    change HasFDerivAt (loopCLM k) (loopCLM k) a
    exact (loopCLM (κ := κ) k).hasFDerivAt (x := a)
  have hS := (SmoothPaths.hasFDerivAt_superpose
    (hH.differentiable (by simp)) (hH.fderiv_right (m := ∞) (by simp)).continuous (loop k a)).comp
      a hl
  have hi := average.hasFDerivAt.comp a hS
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (potential k H) _ a at hi
  apply hi.congr_fderiv
  ext b
  change (∫ t : Time, fderiv ℝ H (loop k a t) (loop k b t) ∂μ) =
    inner (𝕜 := ℝ) (project k (gradLoop k hH a)) b
  simp_rw [← inner_gradient_left]
  exact integral_inner_loop k (gradLoop k hH a) b

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.QuadraticAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace DiagonalQuadratic
noncomputable section
open Finset
open scoped ComplexConjugate ContDiff
variable {α : Type u112} [Fintype α]

 theorem real_inner_eq_sum (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) a b = ∑ p, inner (𝕜 := ℝ) (a p) (b p) := by
  exact PiLp.inner_apply a b

 theorem inner_diag (w : α → ℝ) (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) (diag w a) b = ∑ p, w p * inner (𝕜 := ℝ) (a p) (b p) := by
  rw [real_inner_eq_sum]
  simp only [diag_apply, real_inner_smul_left]

 theorem self_adjoint (w : α → ℝ) (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) (diag w a) b = inner (𝕜 := ℝ) a (diag w b) := by
  rw [inner_diag, real_inner_eq_sum]
  simp only [diag_apply, real_inner_smul_right]

 theorem energy_eq_inner (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    energy w a = inner (𝕜 := ℝ) (diag w a) a := by
  rw [inner_diag]
  simp only [energy, real_inner_self_eq_norm_sq]

 theorem hasGradientAt_energy (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    HasGradientAt (energy w) ((2 : ℝ) • diag w a) a := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (diagCLM w).hasFDerivAt.inner ℝ (hasFDerivAt_id a)
  simp only [diagCLM_apply] at h
  change HasFDerivAt (fun x => inner (𝕜 := ℝ) (diag w x) x) _ a at h
  simp_rw [← energy_eq_inner] at h
  apply h.congr_fderiv
  ext b
  change inner (𝕜 := ℝ) (diag w a) b + inner (𝕜 := ℝ) (diag w b) a =
    inner (𝕜 := ℝ) ((2 : ℝ) • diag w a) b
  rw [real_inner_smul_left, self_adjoint w b a]
  rw [real_inner_comm b (diag w a)]
  ring

end
end DiagonalQuadratic

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_7_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 theorem hasGradientAt_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) :
    HasGradientAt (action k H)
      ((2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a - project k (gradLoop k hH a)) a := by
  have h := (hasGradientAt_energy (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a).hasFDerivAt.sub
    (hasGradientAt_potential k hH a).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (action k H) _ a at h
  apply h.congr_fderiv
  ext b
  simp only [map_sub]

 theorem gradient_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) : gradient (action k H) a =
      (2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a - project k (gradLoop k hH a) :=
  (hasGradientAt_action k hH a).gradient

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_8_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 theorem loop_smul (k : ι → ℤ) (r : ℝ) (a : Coeff ι κ) :
    loop k (r • a) = r • loop k a := (loopCLM k).map_smul r a

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_9_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GalerkinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_10_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_11_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_12
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

omit [Fintype ι] [Fintype κ] in
 theorem mode_velocityCoeff (k : ι → ℤ) (a : Coeff ι κ) (i : ι) :
    mode (velocityCoeff k a) i = (2*(Real.pi : ℂ)*Complex.I*(k i : ℂ)) • mode a i := by
  ext j
  simp only [mode_apply, velocityCoeff, PiLp.smul_apply, diag_apply,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  simp only [map_mul, map_intCast, map_ofNat]
  change Complex.I * ((2 : ℂ) * (((Real.pi : ℂ)*(k i : ℂ))*a (i,j))) =
    (2*(Real.pi : ℂ)*Complex.I*(k i : ℂ))*a (i,j)
  ring

 theorem hasDerivAt_loop (k : ι → ℤ) (a : Coeff ι κ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => loop k a (s : Time)) (loop k (velocityCoeff k a) (t : Time)) t := by
  have hs := HasDerivAt.fun_sum (u := univ) (fun i _ =>
    (hasDerivAt_fourier (1 : ℝ) (k i) t).smul_const (mode a i))
  change HasDerivAt (fun s : ℝ => loop k a (s : Time)) _ t at hs
  apply hs.congr_deriv
  simp only [loop_apply, mode_velocityCoeff, smul_smul, div_one, Complex.ofReal_one]
  apply sum_congr rfl
  intro i _
  congr 1
  ring

 theorem intervalIntegral_eq_average {E : Type u113} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Time → E) : (∫ t in (0:ℝ)..1, f (t : Time)) = ∫ t : Time, f t ∂μ := by
  rw [AddCircle.integral_haarAddCircle]
  simpa only [zero_add, inv_one, one_smul] using AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_13_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace L2Paths
noncomputable section
open Set intervalIntegral
open MeasureTheory (volume)
open scoped Topology BoundedContinuousFunction
variable {E : Type u114} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem integral_sq_le (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  rcases hab.eq_or_lt with he | hab
  · subst b
    simp
  let avg := ∫ t in a..b, f t
  let L := b-a
  have hL : 0 < L := sub_pos.mpr hab
  have hnon : 0 ≤ ∫ t in a..b, (L*f t-avg)^2 :=
    integral_nonneg_of_forall hab.le (fun _ => sq_nonneg _)
  have he (t : ℝ) : (L*f t-avg)^2 = L^2*(f t)^2-(2*L*avg)*f t+avg^2 := by ring
  simp_rw [he] at hnon
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const] at hnon
  · simp only [smul_eq_mul] at hnon
    change 0 ≤ L^2*(∫ t in a..b, (f t)^2)-(2*L*avg)*avg+L*avg^2 at hnon
    change avg^2 ≤ L*(∫ t in a..b, (f t)^2)
    nlinarith
  · exact (hf.pow 2).intervalIntegrable _ _ |>.const_mul _
  · exact hf.intervalIntegrable _ _ |>.const_mul _
  · exact (((hf.pow 2).const_mul _).sub (hf.const_mul _)).intervalIntegrable _ _
  · exact intervalIntegrable_const

 theorem norm_sub_sq_le (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {a b : ℝ} (hab : a ≤ b) :
    ‖x b-x a‖^2 ≤ (b-a)*(∫ t in a..b, ‖v t‖^2) := by
  have he := integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hv.intervalIntegrable a b)
  have hn : ‖x b-x a‖ ≤ ∫ t in a..b, ‖v t‖ := by
    rw [← he]
    exact norm_integral_le_integral_norm hab
  have hi := integral_sq_le (fun t => ‖v t‖) hv.norm hab
  have hs : ‖x b-x a‖^2 ≤ (∫ t in a..b, ‖v t‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hs.trans hi

 theorem norm_sub_sq_le_global (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {D : ℝ}
    (hD : (∫ t in (0:ℝ)..1, ‖v t‖^2) ≤ D^2)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    ‖x b-x a‖^2 ≤ D^2*|b-a| := by
  wlog hab : a ≤ b generalizing a b
  · have h := this hb ha (le_of_not_ge hab)
    rwa [norm_sub_rev, abs_sub_comm] at h
  have hi := integral_mono_interval (μ := volume) ha.1 hab hb.2
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖v t‖)) ((hv.norm.pow 2).intervalIntegrable 0 1)
  have hc := norm_sub_sq_le x v hv hd hab
  have hm := mul_le_mul_of_nonneg_left (hi.trans hD) (sub_nonneg.mpr hab)
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  exact hc.trans (by nlinarith)

 theorem norm_bound (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hxm : (∫ t in (0:ℝ)..1, ‖x t‖^2) ≤ A^2)
    (hvm : (∫ t in (0:ℝ)..1, ‖v t‖^2) ≤ D^2)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖x t‖ ≤ A+D := by
  have hx : Continuous x := continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  have hpoint (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖x t‖ ≤ ‖x s‖+D := by
    have hdiff := norm_sub_sq_le_global x v hv hd hvm hs ht
    have hab : |t-s| ≤ 1 := (abs_le).mpr ⟨by linarith [ht.1,hs.2], by linarith [ht.2,hs.1]⟩
    have hmul := mul_le_mul_of_nonneg_left hab (sq_nonneg D)
    have hn : ‖x t-x s‖ ≤ D := by nlinarith [norm_nonneg (x t-x s)]
    have htri := norm_sub_le (x t-x s) (-x s)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
    linarith
  have hi : ∫ s in (0:ℝ)..1, ‖x t‖ ≤ ∫ s in (0:ℝ)..1, ‖x s‖+D :=
    integral_mono_on (by norm_num) intervalIntegrable_const
      ((hx.norm.add continuous_const).intervalIntegrable _ _) hpoint
  rw [integral_const, integral_add (hx.norm.intervalIntegrable _ _) intervalIntegrable_const,
    integral_const] at hi
  simp only [sub_zero, one_smul] at hi
  have hcs := integral_sq_le (fun s => ‖x s‖) hx.norm (show (0:ℝ) ≤ 1 by norm_num)
  simp only [sub_zero, one_mul] at hcs
  have hmean : ∫ t_1 in (0:ℝ)..1, ‖x t_1‖ ≤ A := by
    nlinarith [integral_nonneg_of_forall (μ := volume) (show (0:ℝ) ≤ 1 by norm_num) (fun s => norm_nonneg (x s))]
  linarith

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem exists_subsequence [ProperSpace E] (u : ℕ → C(Segment,E)) {D R : ℝ}
    (hmod : ∀ n (t s : Segment), dist (u n t) (u n s)^2 ≤ D^2*dist t s)
    (hbound : ∀ n (t : Segment), ‖u n t‖ ≤ R) :
    ∃ x : C(Segment,E), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  let eqv := ContinuousMap.isometryEquivBoundedOfCompact Segment E
  let v : ℕ → (Segment →ᵇ E) := fun n => eqv (u n)
  have heq : Equicontinuous ((↑) : Set.range v → Segment → E) := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε^2/(D^2+1), by positivity, fun t s hts f => ?_⟩
    rcases f.property with ⟨n,hn⟩
    have hm := hmod n t s
    have hd : (D^2+1)*dist t s < ε^2 := by
      have := (lt_div_iff₀ (by positivity : 0 < D^2+1)).mp hts
      linarith
    rw [← hn]
    change dist (u n t) (u n s) < ε
    nlinarith [(dist_nonneg : 0 ≤ dist (u n t) (u n s)), (dist_nonneg : 0 ≤ dist t s)]
  have hc : IsCompact (closure (Set.range v)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:E) R)
      (isCompact_closedBall _ _) (Set.range v)
      (fun f t hf => by
        rcases hf with ⟨n,rfl⟩
        change dist (u n t) (0:E) ≤ R
        simpa only [dist_zero_right] using hbound n t) heq
  obtain ⟨x,hx,φ,hφ,ht⟩ := hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨eqv.symm x,φ,hφ,?_⟩
  exact eqv.symm.continuous.continuousAt.tendsto.comp ht

attribute [local instance] OAI.L2Paths.instFactLtRealOfNat_solutions
omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem restriction_isometry : Isometry (restriction (E := E)) := by
  rw [isometry_iff_dist_eq]
  intro x y
  apply le_antisymm
  · apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist x y)).2
    intro t
    exact ContinuousMap.dist_apply_le_dist (t.val : Time)
  · apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist (restriction x) (restriction y))).2
    intro t
    let r := AddCircle.equivIoc (1 : ℝ) 0 t
    have hr : r.val ∈ Set.Icc (0:ℝ) 1 := ⟨r.property.1.le, by simpa using r.property.2⟩
    have h := ContinuousMap.dist_apply_le_dist (f := restriction x) (g := restriction y) ⟨r.val,hr⟩
    simpa only [restriction, ContinuousMap.coe_mk, r, AddCircle.coe_equivIoc] using h

omit [NormedSpace ℝ E] in
 theorem exists_periodic_subsequence [ProperSpace E] (u : ℕ → C(Time,E)) {D R : ℝ}
    (hmod : ∀ n (t s : Segment), dist (u n (t.val : Time)) (u n (s.val : Time))^2 ≤ D^2*dist t s)
    (hbound : ∀ n (t : Segment), ‖u n (t.val : Time)‖ ≤ R) :
    ∃ x : C(Time,E), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  obtain ⟨x,φ,hφ,ht⟩ := exists_subsequence (fun n => restriction (u n)) hmod hbound
  have hc' : Cauchy (Filter.map restriction (Filter.map (u ∘ φ) Filter.atTop)) := by
    rw [Filter.map_map]
    exact ht.cauchySeq
  have hc : CauchySeq (u ∘ φ) :=
    restriction_isometry.isUniformInducing.cauchy_map_iff.mp hc'
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨y,φ,hφ,hy⟩

end
end L2Paths

namespace PeriodicFourier
noncomputable section
open MeasureTheory AddCircle Finset Set
open scoped ComplexConjugate Topology
open FourierPolynomial (integrable_continuous)

 attribute [local instance] OAI.PeriodicFourier.instFactLtRealOfNat_solutions
theorem coefficient_ext {f g : C(Time,ℂ)} (h : ∀ n, coefficient n f = coefficient n g) : f = g := by
  have hz (n : ℤ) : fourierCoeff (f-g) n = 0 := by
    change coefficient n (f-g) = 0
    rw [map_sub, h, sub_self]
  have hs : Summable (fourierCoeff (f-g)) := by
    simpa only [funext hz] using (summable_zero : Summable (fun _ : ℤ => (0:ℂ)))
  have hh := hasSum_fourier_series_of_summable hs
  simp only [hz, zero_smul] at hh
  have he : f-g = 0 := hh.unique hasSum_zero
  exact sub_eq_zero.mp he

 theorem coefficient_const (n : ℤ) (c : ℂ) :
    coefficient n (ContinuousMap.const Time c) = if n = 0 then c else 0 := by
  rw [coefficient_apply, fourierCoeff]
  simp only [ContinuousMap.coe_const, Function.const_apply, smul_eq_mul]
  rw [integral_mul_const, FourierPolynomial.integral_fourier]
  simp only [neg_eq_zero]
  split_ifs <;> simp

 theorem constant_of_nonzero_coeff {f : C(Time,ℂ)}
    (h : ∀ n : ℤ, n ≠ 0 → coefficient n f = 0) :
    f = ContinuousMap.const Time (coefficient 0 f) := by
  apply coefficient_ext
  intro n
  rw [coefficient_const]
  by_cases hn : n = 0
  · subst n; simp
  · simp [hn,h n hn]

 theorem coefficient_eq_on (f : C(Time,ℂ)) (n : ℤ) :
    fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun t : ℝ => f (t : Time)) n = coefficient n f := by
  rw [fourierCoeffOn_eq_integral, coefficient_apply, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp

 theorem derivative_coefficient (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0)
    {n : ℤ} (hn : n ≠ 0) :
    (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) * coefficient n (periodicPrimitive v hzero) = coefficient n v := by
  have hp := periodic_primitive v hzero
  have hi := fourierCoeffOn_of_hasDerivAt (show (0:ℝ) < 1 by norm_num) hn
    (fun t _ => hasDerivAt_primitive v t)
    ((v.continuous.comp continuous_quot_mk).intervalIntegrable 0 1)
  have ht : primitive v 1 = primitive v 0 := by simpa using hp 0
  simp only [ht, sub_self, mul_zero, Complex.ofReal_one, Complex.ofReal_zero, sub_zero, one_mul, zero_sub] at hi
  change fourierCoeffOn _ (fun t : ℝ => periodicPrimitive v hzero (t : Time)) n =
    1 / (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * -fourierCoeffOn _ (fun t : ℝ => v (t : Time)) n at hi
  rw [coefficient_eq_on, coefficient_eq_on] at hi
  rw [hi]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

 theorem hasDerivAt_of_coefficients (x v : C(Time,ℂ))
    (h : ∀ n : ℤ, coefficient n v = (2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*coefficient n x)
    (t : ℝ) : HasDerivAt (fun s : ℝ => x (s : Time)) (v (t : Time)) t := by
  have hz : coefficient 0 v = 0 := by simpa using h 0
  let y := periodicPrimitive v hz
  have hc : x-y = ContinuousMap.const Time (coefficient 0 (x-y)) := by
    apply constant_of_nonzero_coeff
    intro n hn
    rw [map_sub]
    have he := derivative_coefficient v hz hn
    rw [h n] at he
    have hn' : (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
      exact_mod_cast hn
    have heq := (mul_left_cancel₀ hn') he
    change coefficient n x-coefficient n (periodicPrimitive v hz) = 0
    exact sub_eq_zero.mpr heq.symm
  have hx (s : ℝ) : x (s : Time) = primitive v s+coefficient 0 (x-y) := by
    have he := congrArg (fun f : C(Time,ℂ) => f (s : Time)) hc
    change x (s : Time)-primitive v s = coefficient 0 (x-y) at he
    exact sub_eq_iff_eq_add'.mp he
  simpa only [← hx] using (hasDerivAt_primitive v t).add_const (coefficient 0 (x-y))

end
end PeriodicFourier

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicSolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_14
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
open DiagonalQuadratic FourierPolynomial

 local instance instFactLtRealOfNat_solutions_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

 theorem positiveMode_injective (N : ℕ) : Function.Injective (positiveMode N) := by
  intro i j hij
  apply Fin.ext
  simpa [positiveMode] using hij

 theorem frequency_injective (N : ℕ) : Function.Injective (frequency N) := by
  intro i j hij
  cases i <;> cases j
  · simp only [frequency, Sum.elim_inl, negativeMode, neg_inj, Nat.cast_inj] at hij
    exact congrArg Sum.inl (Fin.ext hij)
  · simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode, Nat.cast_add, Nat.cast_one] at hij
    omega
  · simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode, Nat.cast_add, Nat.cast_one] at hij
    omega
  · simp only [frequency, Sum.elim_inr, Nat.cast_inj] at hij
    exact congrArg Sum.inr (positiveMode_injective N hij)

 theorem frequency_exhausts (m : ℤ) : ∀ᶠ N in atTop, m ∈ Set.range (frequency N) := by
  cases m with
  | ofNat m =>
    cases m with
    | zero =>
      filter_upwards [] with N
      exact ⟨Sum.inl ⟨0,Nat.succ_pos N⟩, by simp [frequency,negativeMode]⟩
    | succ m =>
      filter_upwards [eventually_ge_atTop m] with N hN
      exact ⟨Sum.inr ⟨m,by omega⟩, by simp [frequency,positiveMode]⟩
  | negSucc m =>
    filter_upwards [eventually_ge_atTop (m+1)] with N hN
    exact ⟨Sum.inl ⟨m+1,by omega⟩, by simp [frequency,negativeMode,Int.negSucc_eq]⟩

 variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HamiltonianODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace HamiltonianODE
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
open FourierPolynomial DiagonalQuadratic
local instance instFactLtRealOfNat_solutions_rc74a79_2 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {κ : Type u116} [Fintype κ]

end
end HamiltonianODE

namespace HamiltonianODE
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic
variable {κ : Type u118} [Fintype κ]

end
end HamiltonianODE

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HamiltonianGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace HamiltonianGrowth
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u119} [Fintype κ]

end
end HamiltonianGrowth

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type u120} [Fintype κ]

end
end HamiltonianPeriodic

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.EmbeddingInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace EmbeddingInverse
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {E : Type u121} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end
end EmbeddingInverse

namespace ComplexSymplectic
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE
variable {κ : Type u122} [Fintype κ]

end
end ComplexSymplectic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace SmoothProfiles
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

end
end SmoothProfiles

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.ExteriorHamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE SmoothProfiles EmbeddingInverse
variable {κ : Type u123} [Fintype κ]

end
end PushedBall

namespace ExteriorHamiltonian
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth SmoothProfiles
variable {κ : Type u124} [Fintype κ]

end
end ExteriorHamiltonian

namespace ExteriorHamiltonian
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
variable {κ : Type u125} [Fintype κ]

end
end ExteriorHamiltonian

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles ExteriorHamiltonian
variable {κ : Type u126} [Fintype κ]

end
end PushedBall

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.Nonsqueezing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace CylinderParameters
noncomputable section
open Set Filter Finset
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u127} [Fintype κ] [DecidableEq κ]

end
end CylinderParameters

namespace CylinderNonsqueezing
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
open ExteriorHamiltonian PushedBall CylinderParameters
variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end CylinderNonsqueezing
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.UpperBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace CylinderNonsqueezing
noncomputable section
open Set
open scoped ContDiff
open FourierPolynomial
variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end CylinderNonsqueezing
end

end OAI
end
end

section
/-!
Blueprint, Part M: elementary properties of `cEHZ` on convex domains, and monotonicity under
inclusion from Clarke's dual action principle in length form
(`Viterbo.exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq`).
-/

open MeasureTheory Set OAI.SymmetricPolar
open scoped ENNReal Pointwise

namespace Viterbo.CM

variable {n : ℕ}

/-! ## Helpers -/

/-! ### Absolutely continuous loops -/

/-! ### Support functions -/

/-! ### Translation -/

/-! ### Scaling -/

/-! ### Positivity of the action -/

end Viterbo.CM
end

section
set_option autoImplicit false

open scoped ENNReal ContDiff Pointwise

namespace Viterbo.Capacities

open OAI.SymmetricPolar Set Topology

/-! ## Generic facts about symplectic embeddings -/

/-! ## The bridge `ℝ²ⁿ ≅ ℂⁿ`, `(q, p) ↦ q + i p` -/


/-! ## Non-squeezing in phase-space form -/

/-! ## The two capacities -/

end Viterbo.Capacities
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {H : Type} {E : Type} {F : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-!
# Blueprint: `c_EHZ` extends to a symplectic capacity (HKO p. 2)

Target: `Viterbo.exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ`.

Route (see `proofs/capacity/BRIEF.md` in the mission repo):
* the capacity is the envelope `c(U) = ⨆ {cEHZ K : K convex domain, K ↪ U}`;
* everything reduces to (A) `cEHZ_le_of_hse`: `K ↪ L` between convex domains gives
  `cEHZ K ≤ cEHZ L`, proved by a Hofer–Zehnder argument on OpenAI's Galerkin engine
  (`OAI.FourierPolynomial`, `OAI.HamiltonianPeriodic`), with
  - linking along a trigonometric approximation of a minimal characteristic of `L` (Parts W, C),
  - compactness from the identity `Φ = ∫ (⟨∇H x, x⟩/2 - H x)` and a homogeneous limit (Parts E1, E2a),
  - mollified gauges for smoothness (Part M) and slow profiles on `K` (Part K).
-/
/-! ## Shared definitions -/
/-! ## Part E1: the linking lemma under a Cerami condition (finite dimension) -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE2a
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic OAI.DiagonalQuadratic
local instance instFactOneE2a : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

end Viterbo.Cap.PartE2a
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE2a
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic OAI.DiagonalQuadratic
variable {ι κ : Type} [Fintype ι] [Fintype κ]
/-- `Φ(a) - ⟨∇Φ(a), a⟩/2 = ∫ (⟨∇H, x⟩/2 - H)` along the Galerkin loop. -/
theorem action_sub_half_inner (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) :
    FourierPolynomial.action k H a - inner (𝕜 := ℝ) (gradient (FourierPolynomial.action k H) a) a / 2 =
      meanAction hH (loop k a) := by
  have hi := integral_inner_loop k (gradLoop k hH a) a
  have hgi : Integrable (fun t : Time =>
      inner (𝕜 := ℝ) (gradient H (loop k a t)) (loop k a t)) μ :=
    integrable_continuous ((gradLoop k hH a).continuous.inner (loop k a).continuous)
  have hpi : Integrable (fun t : Time => H (loop k a t)) μ :=
    integrable_continuous (hH.continuous.comp (loop k a).continuous)
  unfold meanAction
  rw [integral_sub (hgi.div_const 2) hpi, integral_div]
  change _ = (∫ t : Time, inner (𝕜 := ℝ) (gradLoop k hH a t) (loop k a t) ∂μ)/2 -
    potential k H a
  rw [hi, gradient_action k hH, inner_sub_left, real_inner_smul_left, ← energy_eq_inner]
  unfold FourierPolynomial.action
  ring

theorem norm_project_gradLoop_le (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) {C : ℝ}
    (hgrow : ∀ z, ‖gradient H z‖ ≤ C * (1 + ‖z‖)) (a : Coeff ι κ) :
    ‖project k (gradLoop k hH a)‖ ≤ 2 * C * (1 + ‖a‖) := by
  have hC : 0 ≤ C := by
    have h := hgrow 0
    simp only [norm_zero, add_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have hb := project_bessel k hk (gradLoop k hH a)
  have hpt : ∀ t : Time, ‖gradLoop k hH a t‖ ^ 2 ≤ 2 * C ^ 2 * (1 + ‖loop k a t‖ ^ 2) := by
    intro t
    have h1 := hgrow (loop k a t)
    have h2 : ‖gradLoop k hH a t‖ ≤ C * (1 + ‖loop k a t‖) := h1
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [sq_nonneg (1 - ‖loop k a t‖), sq_nonneg C]
  have hint : (∫ t : Time, ‖gradLoop k hH a t‖ ^ 2 ∂μ) ≤ 2 * C ^ 2 * (1 + ‖a‖ ^ 2) := by
    calc
      _ ≤ ∫ t : Time, 2 * C ^ 2 * (1 + ‖loop k a t‖ ^ 2) ∂μ :=
        integral_mono (integrable_continuous ((gradLoop k hH a).continuous.norm.pow 2))
          (integrable_continuous (continuous_const.mul
            (continuous_const.add ((loop k a).continuous.norm.pow 2)))) hpt
      _ = 2 * C ^ 2 * (1 + ‖a‖ ^ 2) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          (integrable_continuous (f := fun t : Time => ‖loop k a t‖ ^ 2)
            ((loop k a).continuous.norm.pow 2))]
        rw [integral_loop_norm_sq k hk]
        simp
  have hsq : ‖project k (gradLoop k hH a)‖ ^ 2 ≤ (2 * C * (1 + ‖a‖)) ^ 2 := by
    nlinarith [sq_nonneg (1 - ‖a‖), sq_nonneg C, norm_nonneg a]
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

theorem norm_velocityCoeff_le (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) :
    ‖velocityCoeff k a‖ ≤ ‖gradient (FourierPolynomial.action k H) a‖ + ‖project k (gradLoop k hH a)‖ := by
  have he : (2 : ℝ) • diag (fun p => Real.pi * (k p.1 : ℝ)) a =
      gradient (FourierPolynomial.action k H) a + project k (gradLoop k hH a) := by
    rw [gradient_action k hH]; abel
  simp only [velocityCoeff, he, norm_smul, Complex.norm_I, one_mul]
  exact norm_add_le _ _

omit [Fintype ι] [Fintype κ] in
theorem velocityCoeff_smul (k : ι → ℤ) (r : ℝ) (a : Coeff ι κ) :
    velocityCoeff k (r • a) = r • velocityCoeff k a := by
  ext p
  simp only [velocityCoeff, PiLp.smul_apply, diag_apply, smul_eq_mul,
    RCLike.real_smul_eq_coe_mul]
  ring

theorem exists_small_point (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) {R γ₀ : ℝ}
    (hγ : 0 < γ₀) (hout : ∀ z, R ≤ ‖z‖ → inner (𝕜 := ℝ) (gradient H z) z / 2 - H z ≤ -γ₀)
    (a : Coeff ι κ) (hpos : 0 < meanAction hH (loop k a)) :
    ∃ t : Time, ‖loop k a t‖ < R := by
  by_contra hcon
  push Not at hcon
  have hle : meanAction hH (loop k a) ≤ -γ₀ := by
    unfold meanAction
    calc
      _ ≤ ∫ _ : Time, -γ₀ ∂μ := integral_mono
          (integrable_continuous ((((contDiff_gradient_function hH).continuous.comp
            (loop k a).continuous).inner (loop k a).continuous).div_const 2 |>.sub
            (hH.continuous.comp (loop k a).continuous)))
          (integrable_const _) (fun t => hout _ (hcon t))
      _ = -γ₀ := by simp
  linarith

omit [Fintype ι] in
theorem project_smul (k : ι → ℤ) (s : ℝ) (f : C(Time, Vector κ)) :
    project k (s • f) = s • project k f := by
  ext p
  simp only [project_apply, ContinuousMap.smul_apply, PiLp.smul_apply]
  have he : (fun t : Time => s • f t p.2) = fun t => (s : ℂ) • f t p.2 := by
    funext t; simp [Complex.real_smul]
  rw [he, show (fun t : Time => (s : ℂ) • f t p.2) = (s : ℂ) • (fun t => f t p.2) from rfl,
    fourierCoeff.const_smul]
  simp [Complex.real_smul]

/-- The Galerkin equation, mode by mode, rescaled by `s`. -/
theorem coefficient_rescaled (k : ι → ℤ) (hk : Function.Injective k) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (s : ℝ) (a : Coeff ι κ) (i : ι) (j : κ) :
    PeriodicFourier.coefficient (k i) (coordPath j (s • gradLoop k hH a)) =
      (2 * (Real.pi : ℂ) * (k i : ℂ)) *
          PeriodicFourier.coefficient (k i) (coordPath j (loop k (s • a))) -
        (s : ℂ) * gradient (FourierPolynomial.action k H) a (i, j) := by
  have he : project k (gradLoop k hH a) =
      (2 : ℝ) • diag (fun p : ι × κ => Real.pi * (k p.1 : ℝ)) a -
        gradient (FourierPolynomial.action k H) a := by
    rw [gradient_action k hH]; abel
  change project k (s • gradLoop k hH a) (i, j) =
    (2 * (Real.pi : ℂ) * (k i : ℂ)) * project k (loop k (s • a)) (i, j) -
      (s : ℂ) * gradient (FourierPolynomial.action k H) a (i, j)
  rw [project_loop k hk, project_smul, he]
  simp only [PiLp.smul_apply, PiLp.sub_apply, diag_apply, Complex.real_smul]
  push_cast
  ring

theorem loop_modulus (k : ι → ℤ) (hk : Function.Injective k) (b : Coeff ι κ) {D : ℝ}
    (hv : ‖velocityCoeff k b‖ ≤ D) (t s : L2Paths.Segment) :
    dist (loop k b (t.val : Time)) (loop k b (s.val : Time)) ^ 2 ≤ D ^ 2 * dist t s := by
  have hb : (∫ t in (0:ℝ)..1, ‖loop k (velocityCoeff k b) (t : Time)‖ ^ 2) ≤ D ^ 2 := by
    rw [intervalIntegral_eq_average (fun t : Time => ‖loop k (velocityCoeff k b) t‖ ^ 2),
      integral_loop_norm_sq k hk]
    exact pow_le_pow_left₀ (norm_nonneg _) hv 2
  have h := L2Paths.norm_sub_sq_le_global
    (fun t : ℝ => loop k b (t : Time)) (fun t : ℝ => loop k (velocityCoeff k b) (t : Time))
    ((loop k (velocityCoeff k b)).continuous.comp continuous_quot_mk)
    (hasDerivAt_loop k b) hb s.property t.property
  simpa only [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, Real.norm_eq_abs] using h

theorem loop_bound (k : ι → ℤ) (hk : Function.Injective k) (b : Coeff ι κ) {D : ℝ}
    (hD : 0 ≤ D) (hb1 : ‖b‖ ≤ 1) (hv : ‖velocityCoeff k b‖ ≤ D) (t : L2Paths.Segment) :
    ‖loop k b (t.val : Time)‖ ≤ 1 + D := by
  have hx : (∫ t in (0:ℝ)..1, ‖loop k b (t : Time)‖ ^ 2) ≤ 1 ^ 2 := by
    rw [intervalIntegral_eq_average (fun t : Time => ‖loop k b t‖ ^ 2),
      integral_loop_norm_sq k hk]
    exact pow_le_pow_left₀ (norm_nonneg _) hb1 2
  have hvv : (∫ t in (0:ℝ)..1, ‖loop k (velocityCoeff k b) (t : Time)‖ ^ 2) ≤ D ^ 2 := by
    rw [intervalIntegral_eq_average (fun t : Time => ‖loop k (velocityCoeff k b) t‖ ^ 2),
      integral_loop_norm_sq k hk]
    exact pow_le_pow_left₀ (norm_nonneg _) hv 2
  exact L2Paths.norm_bound
    (fun t : ℝ => loop k b (t : Time)) (fun t : ℝ => loop k (velocityCoeff k b) (t : Time))
    ((loop k (velocityCoeff k b)).continuous.comp continuous_quot_mk)
    (hasDerivAt_loop k b) zero_le_one hD hx hvv t.property

theorem loop_bound_all (k : ι → ℤ) (hk : Function.Injective k) (b : Coeff ι κ) {D : ℝ}
    (hD : 0 ≤ D) (hb1 : ‖b‖ ≤ 1) (hv : ‖velocityCoeff k b‖ ≤ D) (t : Time) :
    ‖loop k b t‖ ≤ 1 + D := by
  let s := AddCircle.equivIoc (1 : ℝ) 0 t
  have hs : s.val ∈ Set.Icc (0:ℝ) 1 := ⟨s.property.1.le, by simpa using s.property.2⟩
  have h := loop_bound k hk b hD hb1 hv ⟨s.val, hs⟩
  simpa only [s, AddCircle.coe_equivIoc] using h

omit [Fintype ι] in
/-- Gronwall: a periodic solution of `ẏ = i V(y)` with `‖V z‖ ≤ C ‖z‖` vanishing once is `0`. -/
theorem eq_zero_of_ode {V : Vector κ → Vector κ} {C : ℝ} (hlin : ∀ z, ‖V z‖ ≤ C * ‖z‖)
    (Y : C(Time, Vector κ))
    (hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Y (s : Time)) (Complex.I • V (Y (t : Time))) t)
    (t₀ : Time) (h0 : Y t₀ = 0) : Y = 0 := by
  obtain ⟨s₀, rfl⟩ := QuotientAddGroup.mk_surjective t₀
  set Z : ℝ → Vector κ := fun s => Y (s : Time) with hZ
  have hper : Function.Periodic Z 1 := fun s => by
    simp only [hZ, AddCircle.coe_add_period]
  have hgr : ∀ b, s₀ ≤ b → Z b = 0 := by
    intro b hb
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := Z)
      (f' := fun s => Complex.I • V (Z s)) (δ := 0) (K := C) (ε := 0) (a := s₀) (b := b)
      (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => (hd s).hasDerivWithinAt)
      (by simp only [hZ]; rw [show ((s₀ : ℝ) : Time) = QuotientAddGroup.mk s₀ from rfl, h0,
        norm_zero])
      (fun s _ => by
        rw [norm_smul, Complex.norm_I, one_mul, add_zero]; exact hlin _) b ⟨hb, le_rfl⟩
    rw [gronwallBound_ε0_δ0] at h
    exact norm_le_zero_iff.mp h
  ext1 t
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨n, hn⟩ := exists_nat_ge (s₀ - s)
  have h1 := hper.nat_mul n s
  have h2 := hgr (s + n * 1) (by linarith)
  rw [h1] at h2
  exact h2

end Viterbo.Cap.PartE2a
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE2a
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic OAI.DiagonalQuadratic
variable {κ : Type} [Fintype κ] [DecidableEq κ]
omit [DecidableEq κ] in
theorem no_bad_sequence {H : Vector κ → ℝ} {V : Vector κ → Vector κ} {C R γ₀ : ℝ}
    (hE : EngineHyp H V C R γ₀) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (N : ℕ → ℕ) (hN : ∀ n, n ≤ N n)
    (x : (n : ℕ) → Coeff (Fin (N n + 1) ⊕ Fin (N n + 1)) κ)
    (hxa : ∀ n, a₀ ≤ FourierPolynomial.action (frequency (N n)) H (x n))
    (hxr : ∀ n : ℕ, (n : ℝ) + 1 ≤ ‖x n‖)
    (hxg : ∀ n, (1 + ‖x n‖) *
      ‖gradient (FourierPolynomial.action (frequency (N n)) H) (x n)‖ < a₀) : False := by
  have hH := hE.smooth
  have hkinj : ∀ n, Function.Injective (frequency (N n)) := fun n => frequency_injective (N n)
  have hC : 0 ≤ C := by
    have h := hE.grow 0
    simp only [norm_zero, add_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  set r : ℕ → ℝ := fun n => ‖x n‖ with hr_def
  have hr1 : ∀ n, 1 ≤ r n := fun n => by
    have := hxr n; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; simp only [hr_def]; linarith
  have hrpos : ∀ n, 0 < r n := fun n => lt_of_lt_of_le one_pos (hr1 n)
  set g := fun n => gradient (FourierPolynomial.action (frequency (N n)) H) (x n) with hg_def
  have hg : ∀ n, ‖g n‖ * (1 + r n) < a₀ := fun n => by rw [mul_comm]; exact hxg n
  have hgle : ∀ n, ‖g n‖ ≤ a₀ / r n := fun n => by
    rw [le_div_iff₀ (hrpos n)]; nlinarith [hg n, norm_nonneg (g n)]
  -- the loops visit the ball of radius `R`
  have hsmall : ∀ n, ∃ t : Time, ‖loop (frequency (N n)) (x n) t‖ < R := by
    intro n
    apply exists_small_point (frequency (N n)) hH hE.γpos hE.outer
    rw [← action_sub_half_inner]
    have h1 := real_inner_le_norm (g n) (x n)
    have h2 : ‖g n‖ * ‖x n‖ ≤ ‖g n‖ * (1 + r n) := by
      simp only [hr_def]; nlinarith [norm_nonneg (g n)]
    have h3 := hg n
    have h4 := hxa n
    simp only [hg_def] at h1 h2 h3
    linarith
  choose τ hτ using hsmall
  -- normalization
  set y : (n : ℕ) → Coeff (Fin (N n + 1) ⊕ Fin (N n + 1)) κ := fun n => (r n)⁻¹ • x n
    with hy_def
  have hy1 : ∀ n, ‖y n‖ = 1 := fun n => by
    simp only [hy_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hrpos n)]
    exact inv_mul_cancel₀ (hrpos n).ne'
  set D := a₀ + 4 * C with hD_def
  have hD : 0 ≤ D := by positivity
  have hvel : ∀ n, ‖velocityCoeff (frequency (N n)) (y n)‖ ≤ D := by
    intro n
    simp only [hy_def]
    rw [velocityCoeff_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hrpos n),
      inv_mul_le_iff₀ (hrpos n)]
    have h1 := norm_velocityCoeff_le (frequency (N n)) hH (x n)
    have h2 := norm_project_gradLoop_le (frequency (N n)) (hkinj n) hH hE.grow (x n)
    have h3 : ‖g n‖ ≤ a₀ := by nlinarith [hg n, norm_nonneg (g n), hrpos n]
    have h4 := hr1 n
    simp only [hg_def, hr_def] at h1 h2 h3 h4 ⊢
    nlinarith
  obtain ⟨Y, φ, hφ, hY⟩ := L2Paths.exists_periodic_subsequence
    (fun n => loop (frequency (N n)) (y n))
    (fun n t s => loop_modulus _ (hkinj n) (y n) (hvel n) t s)
    (fun n t => loop_bound _ (hkinj n) (y n) hD (hy1 n).le (hvel n) t)
  set L : ℕ → C(Time, Vector κ) := fun n => loop (frequency (N (φ n))) (y (φ n)) with hL
  have hY' : Tendsto L atTop (𝓝 Y) := hY
  have hLb : ∀ n t, ‖L n t‖ ≤ 1 + D := fun n t =>
    loop_bound_all _ (hkinj _) (y (φ n)) hD (hy1 _).le (hvel _) t
  have hrφ : Tendsto (fun n => r (φ n)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) (fun n => ?_) tendsto_natCast_atTop_atTop
    have h1 := hxr (φ n)
    have h2 : (n:ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    simp only [hr_def]; linarith
  have hinvr : Tendsto (fun n => (r (φ n))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hrφ
  have hdist : Tendsto (fun n => dist (L n) Y) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hY'
  -- the limit vanishes somewhere
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    Y.continuous.norm.continuousOn
  have hY0 : Y t₀ = 0 := by
    have hle : ∀ n, ‖Y t₀‖ ≤ R * (r (φ n))⁻¹ + dist (L n) Y := by
      intro n
      have h1 : ‖Y t₀‖ ≤ ‖Y (τ (φ n))‖ := ht₀ (Set.mem_univ _)
      have h2 : dist (L n (τ (φ n))) (Y (τ (φ n))) ≤ dist (L n) Y :=
        ContinuousMap.dist_apply_le_dist _
      have h3 : ‖L n (τ (φ n))‖ ≤ R * (r (φ n))⁻¹ := by
        simp only [hL, hy_def]
        rw [loop_smul, ContinuousMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos (hrpos _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hτ (φ n)).le (inv_nonneg.mpr (hrpos _).le)
      have h4 := norm_le_norm_add_norm_sub' (Y (τ (φ n))) (L n (τ (φ n)))
      rw [← dist_eq_norm, dist_comm] at h4
      linarith
    have hlim : Tendsto (fun n => R * (r (φ n))⁻¹ + dist (L n) Y) atTop (𝓝 0) := by
      simpa using (hinvr.const_mul R).add hdist
    exact norm_le_zero_iff.mp (ge_of_tendsto' hlim hle)
  -- uniform convergence of the rescaled gradients
  let Vc : C(Vector κ, Vector κ) := ⟨V, hE.contV⟩
  let VY : C(Time, Vector κ) := Vc.comp Y
  set G : ℕ → C(Time, Vector κ) := fun n =>
    (r (φ n))⁻¹ • gradLoop (frequency (N (φ n))) hH (x (φ n)) with hG_def
  have hW : Tendsto (fun n => Vc.comp (L n)) atTop (𝓝 VY) :=
    ((ContinuousMap.continuous_postcomp Vc).tendsto Y).comp hY'
  have hGW : Tendsto (fun n => dist (G n) (Vc.comp (L n))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨r₀, -, hr₀'⟩ := hE.asym (1 + D) (ε / 2) (by positivity)
    obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (tendsto_atTop.mp hrφ r₀)
    refine ⟨n₀, fun n hn => ?_⟩
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
    refine lt_of_le_of_lt ((ContinuousMap.dist_le (by positivity)).2 fun t => ?_)
      (half_lt_self hε)
    have hxL : loop (frequency (N (φ n))) (x (φ n)) t = r (φ n) • L n t := by
      simp only [hL, hy_def, loop_smul, ContinuousMap.smul_apply, smul_smul,
        mul_inv_cancel₀ (hrpos _).ne', one_smul]
    change dist ((r (φ n))⁻¹ • gradient H (loop _ (x (φ n)) t)) (V (L n t)) ≤ ε / 2
    rw [hxL, dist_eq_norm]
    exact hr₀' _ (hn₀ n hn) _ (hLb n t)
  have hG : Tendsto G atTop (𝓝 VY) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) (fun n => dist_triangle (G n) (Vc.comp (L n)) VY)
    simpa using hGW.add (tendsto_iff_dist_tendsto_zero.mp hW)
  -- the Fourier coefficients of the limit
  have hNφ : Tendsto (fun n => N (φ n)) atTop atTop :=
    tendsto_atTop_mono (fun n => (hφ.id_le n).trans (hN _)) tendsto_id
  have hcoef : ∀ (m : ℤ) (j : κ), PeriodicFourier.coefficient m (coordPath j VY) =
      (2 * (Real.pi : ℂ) * (m : ℂ)) * PeriodicFourier.coefficient m (coordPath j Y) := by
    intro m j
    have hc := (PeriodicFourier.coefficient m).continuous.comp (coordPath j).continuous
    have hleft := (hc.tendsto VY).comp hG
    have hright := (tendsto_const_nhds (x := (2 * (Real.pi : ℂ) * (m : ℂ)))).mul
      ((hc.tendsto Y).comp hY')
    have hdiff := hleft.sub hright
    have hzero : Tendsto (fun n => PeriodicFourier.coefficient m (coordPath j (G n)) -
        (2 * (Real.pi : ℂ) * (m : ℂ)) * PeriodicFourier.coefficient m (coordPath j (L n)))
        atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ (by simpa using hinvr.mul_const a₀)
      filter_upwards [hNφ.eventually (frequency_exhausts m)] with n hn
      obtain ⟨i, hi⟩ := hn
      rw [← hi]
      have h := coefficient_rescaled (frequency (N (φ n))) (hkinj _) hH (r (φ n))⁻¹
        (x (φ n)) i (j := j)
      simp only [hG_def, hL, hy_def]
      rw [h, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_inv, abs_of_pos (hrpos _)]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hrpos _).le)
      have h1 := PiLp.norm_apply_le (g (φ n)) (i, j)
      have h2 : ‖g (φ n)‖ ≤ a₀ := by nlinarith [hg (φ n), norm_nonneg (g (φ n)), hrpos (φ n)]
      simp only [hg_def] at h1 h2
      linarith
    have hu := tendsto_nhds_unique hdiff hzero
    exact sub_eq_zero.mp hu
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Y (s : Time))
      (Complex.I • V (Y (t : Time))) t := by
    intro t
    have hj (j : κ) : HasDerivAt (fun s : ℝ => Y (s : Time) j)
        (Complex.I • V (Y (t : Time)) j) t := by
      have hc (m : ℤ) : PeriodicFourier.coefficient m (Complex.I • coordPath j VY) =
          (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) *
            PeriodicFourier.coefficient m (coordPath j Y) := by
        rw [map_smul, hcoef]
        simp only [smul_eq_mul]
        ring
      exact PeriodicFourier.hasDerivAt_of_coefficients (coordPath j Y)
        (Complex.I • coordPath j VY) hc t
    have hp := hasDerivAt_pi.mpr hj
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.hasFDerivAt.comp_hasDerivAt t hp
  have hYz : Y = 0 := eq_zero_of_ode hE.linV Y hderiv t₀ hY0
  -- contradiction with `‖y n‖ = 1`
  rw [hYz] at hdist
  obtain ⟨n, hn⟩ := (hdist.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 2))).exists
  have hpt : ∀ t, ‖L n t‖ ^ 2 ≤ (1 / 2) ^ 2 := fun t => by
    have h1 := ContinuousMap.norm_coe_le_norm (L n) t
    rw [dist_zero_right] at hn
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans hn.le) 2
  have hint := integral_loop_norm_sq (frequency (N (φ n))) (hkinj _) (y (φ n))
  rw [hy1] at hint
  have hle : (∫ t : Time, ‖L n t‖ ^ 2 ∂μ) ≤ ∫ _ : Time, (1 / 2 : ℝ) ^ 2 ∂μ :=
    integral_mono (integrable_continuous ((L n).continuous.norm.pow 2))
      (integrable_const _) hpt
  simp only [hL] at hle
  rw [hint] at hle
  simp at hle
  norm_num at hle

/-- E2a: uniform Cerami bound for the Galerkin functionals above a positive level. -/
theorem galerkin_cerami {H : Vector κ → ℝ} {V : Vector κ → Vector κ} {C R γ₀ : ℝ}
    (hE : EngineHyp H V C R γ₀) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ N₀ : ℕ, ∃ R₁ c₁ : ℝ, 0 < c₁ ∧ ∀ N, N₀ ≤ N →
      ∀ x : Coeff (Fin (N + 1) ⊕ Fin (N + 1)) κ, a₀ ≤ FourierPolynomial.action (frequency N) H x → R₁ ≤ ‖x‖ →
        c₁ ≤ (1 + ‖x‖) * ‖gradient (FourierPolynomial.action (frequency N) H) x‖ := by
  by_contra hcon
  push Not at hcon
  have hseq := fun n : ℕ => hcon n ((n : ℝ) + 1) a₀ ha₀
  choose N hN x hxa hxr hxg using hseq
  exact no_bad_sequence hE ha₀ N hN x hxa hxr hxg

end Viterbo.Cap.PartE2a
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ] [DecidableEq κ]
/-! ## Parts E2a, E2b: the Galerkin engine -/


/-! ## Part C: the cone estimate from a lower bound `H ≥ α gauge_L² - C₀` -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part W: a trigonometric loop beating `α > c_EHZ(L)` -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
/-! ## Part M: mollified gauges -/














end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part K: profiles of a mollified gauge on `K` have only constant `1`-periodic orbits -/

/-! ## Part A1: the bridge from a symplectic embedding of convex domains -/

/-! ## Part A2: one-variable profiles -/


/-! ## Part A3: monotonicity of `c_EHZ` under symplectic embeddings of convex domains -/

/-! ## Part P: the envelope capacity and the target -/

end Viterbo.Cap
end
end

theorem solution : type_of% @Viterbo.Cap.PartE2a.galerkin_cerami := @Viterbo.Cap.PartE2a.galerkin_cerami
