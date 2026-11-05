-- Prove2me | solution 1 for Viterbo.Cap.coneHyp_of_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T17:54:42.358657+00:00
-- url     : https://prove2.me/submissions/28766040-b62b-4e84-a6b0-b20e4dc3d6d2

import Mathlib
import Definitions.Def_OAIQWSP000
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

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_5_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u110} {κ : Type u111} [Fintype ι] [Fintype κ]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_6
variable {ι κ : Type} [Fintype ι] [Fintype κ]

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

end
end DiagonalQuadratic

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_7_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_8_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

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

 theorem energy_joinCoeff (w : (ι ⊕ ν) × κ → ℝ) (a : Coeff ι κ) (b : Coeff ν κ) :
    energy w (joinCoeff a b) = energy (fun p => w (Sum.inl p.1,p.2)) a +
      energy (fun p => w (Sum.inr p.1,p.2)) b := by
  simp only [energy, Fintype.sum_prod_type, Fintype.sum_sum_type,
    joinCoeff_inl, joinCoeff_inr]

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

attribute [local instance] OAI.L2Paths.instFactLtRealOfNat_solutions

end
end L2Paths

namespace PeriodicFourier
noncomputable section
open MeasureTheory AddCircle Finset Set
open scoped ComplexConjugate Topology
open FourierPolynomial (integrable_continuous)

 attribute [local instance] OAI.PeriodicFourier.instFactLtRealOfNat_solutions

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
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ] [DecidableEq κ]
/-! ## Parts E2a, E2b: the Galerkin engine -/


end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartC
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
/-!
# Part C: the cone estimate from a lower bound `H ≥ α gauge_L² - C₀`
-/
/-! ## Gauge and support function -/
lemma bdd_inner {L : Set (Vector κ)} (hLb : Bornology.IsBounded L) (u : Vector κ) :
    BddAbove ((fun x => inner (𝕜 := ℝ) x u) '' L) := by
  obtain ⟨R, hR⟩ := hLb.exists_norm_le
  refine ⟨R * ‖u‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (real_inner_le_norm x u).trans
    (mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg u))

lemma inner_le_supportFn {L : Set (Vector κ)} (hLb : Bornology.IsBounded L) {x : Vector κ}
    (hx : x ∈ L) (u : Vector κ) : inner (𝕜 := ℝ) x u ≤ supportFn L u :=
  le_csSup (bdd_inner hLb u) ⟨x, hx, rfl⟩

lemma supportFn_nonneg {L : Set (Vector κ)} (hLb : Bornology.IsBounded L) (h0 : (0 : Vector κ) ∈ L)
    (u : Vector κ) : 0 ≤ supportFn L u := by
  simpa using inner_le_supportFn hLb h0 u

lemma supportFn_le {L : Set (Vector κ)} (hne : L.Nonempty) {R : ℝ} (hR : ∀ x ∈ L, ‖x‖ ≤ R)
    (u v : Vector κ) : supportFn L u ≤ supportFn L v + R * ‖u - v‖ := by
  have hb : Bornology.IsBounded L := (Metric.isBounded_iff_subset_closedBall 0).2
    ⟨R, fun x hx => by simpa using hR x hx⟩
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  have h1 : inner (𝕜 := ℝ) x u = inner (𝕜 := ℝ) x v + inner (𝕜 := ℝ) x (u - v) := by
    rw [inner_sub_right]; ring
  show inner (𝕜 := ℝ) x u ≤ _
  rw [h1]
  gcongr
  · exact inner_le_supportFn hb hx v
  · exact (real_inner_le_norm x _).trans (mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg _))

lemma continuous_supportFn {L : Set (Vector κ)} (hLb : Bornology.IsBounded L) (hne : L.Nonempty) :
    Continuous (supportFn L) := by
  obtain ⟨R, hR⟩ := hLb.exists_norm_le
  have R0 : 0 ≤ R := by obtain ⟨x, hx⟩ := hne; exact (norm_nonneg x).trans (hR x hx)
  refine (LipschitzWith.of_le_add_mul (K := ⟨R, R0⟩) (fun u v => ?_)).continuous
  have := supportFn_le hne hR u v
  rw [dist_eq_norm]
  exact this

lemma inner_le_gauge_mul {L : Set (Vector κ)} (hLb : Bornology.IsBounded L)
    (h0 : (0 : Vector κ) ∈ interior L) (z u : Vector κ) :
    inner (𝕜 := ℝ) z u ≤ gauge L z * supportFn L u := by
  have habs : Absorbent ℝ L := absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 h0)
  have hh : 0 ≤ supportFn L u := supportFn_nonneg hLb (interior_subset h0) u
  have key : ∀ r, gauge L z < r → inner (𝕜 := ℝ) z u ≤ r * supportFn L u := by
    intro r hr
    obtain ⟨c, hc0, hcr, y, hy, rfl⟩ := exists_lt_of_gauge_lt habs hr
    rw [real_inner_smul_left]
    calc c * inner (𝕜 := ℝ) y u ≤ c * supportFn L u :=
          mul_le_mul_of_nonneg_left (inner_le_supportFn hLb hy u) hc0.le
      _ ≤ r * supportFn L u := mul_le_mul_of_nonneg_right hcr.le hh
  rcases hh.eq_or_lt with h | h
  · have := key (gauge L z + 1) (by linarith)
    rw [← h] at this ⊢; simpa using this
  · have : inner (𝕜 := ℝ) z u / supportFn L u ≤ gauge L z := by
      refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
      rw [div_le_iff₀ h]; exact key r hr
    rwa [div_le_iff₀ h] at this

lemma norm_le_mul_gauge {L : Set (Vector κ)} (hLb : Bornology.IsBounded L)
    (h0 : (0 : Vector κ) ∈ interior L) {R : ℝ} (hR : ∀ x ∈ L, ‖x‖ ≤ R) (z : Vector κ) :
    ‖z‖ ≤ R * gauge L z := by
  have h1 := inner_le_gauge_mul hLb h0 z z
  have h2 : supportFn L z ≤ R * ‖z‖ := by
    have := supportFn_le ⟨0, interior_subset h0⟩ hR z 0
    have h3 : supportFn L 0 = 0 := by
      unfold supportFn
      have : (fun x => inner (𝕜 := ℝ) x (0 : Vector κ)) '' L = {0} := by
        ext y; simp only [inner_zero_right, mem_image, mem_singleton_iff]
        exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨0, interior_subset h0, h.symm⟩⟩
      rw [this, csSup_singleton]
    simpa [h3] using this
  rw [real_inner_self_eq_norm_sq] at h1
  have hg : 0 ≤ gauge L z := gauge_nonneg z
  rcases (norm_nonneg z).eq_or_lt with h | h
  · rw [← h]; exact mul_nonneg ((norm_nonneg _).trans (hR 0 (interior_subset h0))) hg
  · nlinarith

end Viterbo.Cap.PartC
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartC
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Algebra -/
lemma quad_core {Ap δ Ay u v : ℝ} (hA : δ < Ap) (hδ : 0 ≤ δ) (hAy : 0 ≤ Ay)
    (hv : v ^ 2 ≤ δ * Ay) :
    (Ap - δ) * u ^ 2 ≤ Ap * (u + v) ^ 2 + Ap * (Ap - δ) * Ay := by
  have hid : δ * ((Ap - δ) * u ^ 2) + (δ * u + Ap * v) ^ 2 =
      δ * (Ap * (u + v) ^ 2) + Ap * (Ap - δ) * v ^ 2 := by ring
  rcases hδ.eq_or_lt with h | h
  · subst h
    have : v = 0 := by nlinarith
    subst this; simp only [sub_zero, add_zero]
    nlinarith [mul_nonneg (mul_nonneg (hδ.trans hA.le) (hδ.trans hA.le)) hAy]
  · have h2 : Ap * (Ap - δ) * v ^ 2 ≤ Ap * (Ap - δ) * (δ * Ay) :=
      mul_le_mul_of_nonneg_left hv (by nlinarith)
    have : δ * ((Ap - δ) * u ^ 2) ≤ δ * (Ap * (u + v) ^ 2 + Ap * (Ap - δ) * Ay) := by
      nlinarith [sq_nonneg (δ * u + Ap * v)]
    exact le_of_mul_le_mul_left this h

/-- The two-case estimate: `s²A₊ ≤ A_y + Lsq X / (4T)`. -/
lemma quad_main {Ap δ Ay s v X Lsq : ℝ} (hA : δ < Ap) (hδ : 0 ≤ δ) (hAy : 0 ≤ Ay) (hs : 0 ≤ s)
    (hv : v ^ 2 ≤ δ * Ay) (hX : 0 ≤ X) (hL : 0 ≤ Lsq)
    (hCS : 0 ≤ v + s * Ap → 4 * (v + s * Ap) ^ 2 ≤ Lsq * X) :
    s ^ 2 * Ap ≤ Ay + Lsq * X / (4 * (Ap - δ)) := by
  have hT : 0 < Ap - δ := by linarith
  have hAp : 0 < Ap := by linarith
  have hq : 0 ≤ Lsq * X / (4 * (Ap - δ)) := by positivity
  by_cases hw : 0 ≤ v + s * Ap
  · have h1 := quad_core (u := s * Ap) hA hδ hAy hv
    have h2 := hCS hw
    have e : (Ap - δ) * (Ay + Lsq * X / (4 * (Ap - δ))) = (Ap - δ) * Ay + Lsq * X / 4 := by
      field_simp
    refine le_of_mul_le_mul_left ?_ hT
    rw [e]
    have h3 : (Ap - δ) * (s * Ap) ^ 2 = Ap * ((Ap - δ) * (s ^ 2 * Ap)) := by ring
    rw [h3] at h1
    have h4 : (Ap - δ) * (s ^ 2 * Ap) ≤ (s * Ap + v) ^ 2 + (Ap - δ) * Ay := by
      have : Ap * ((Ap - δ) * (s ^ 2 * Ap)) ≤ Ap * ((s * Ap + v) ^ 2 + (Ap - δ) * Ay) := by
        nlinarith
      exact le_of_mul_le_mul_left this hAp
    nlinarith
  · push Not at hw
    have hu : (s * Ap) ^ 2 ≤ v ^ 2 := by nlinarith [mul_nonneg hs hAp.le]
    have : Ap * (s ^ 2 * Ap) ≤ Ap * Ay := by nlinarith
    have := le_of_mul_le_mul_left this hAp
    linarith

/-- Cauchy–Schwarz on `[0,1]` via the discriminant. -/
lemma cs_interval {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, f t * g t) ^ 2 ≤
      (∫ t in (0 : ℝ)..1, f t ^ 2) * ∫ t in (0 : ℝ)..1, g t ^ 2 := by
  set F := ∫ t in (0 : ℝ)..1, f t ^ 2
  set G := ∫ t in (0 : ℝ)..1, g t ^ 2
  set J := ∫ t in (0 : ℝ)..1, f t * g t
  have hq : ∀ r : ℝ, 0 ≤ F * (r * r) + (-2 * J) * r + G := by
    intro r
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (r * f t - g t) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
    have he : ∀ t, (r * f t - g t) ^ 2 = r ^ 2 * f t ^ 2 + (-2 * r) * (f t * g t) + g t ^ 2 :=
      fun t => by ring
    simp_rw [he] at h0
    have i1 : IntervalIntegrable (fun t => r ^ 2 * f t ^ 2) volume 0 1 :=
      (by fun_prop : Continuous fun t => r ^ 2 * f t ^ 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => (-2 * r) * (f t * g t)) volume 0 1 :=
      (by fun_prop : Continuous fun t => (-2 * r) * (f t * g t)).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun t => g t ^ 2) volume 0 1 :=
      (by fun_prop : Continuous fun t => g t ^ 2).intervalIntegrable _ _
    rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
    nlinarith
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

/-! ## Fourier computations -/
local instance instFactOneC : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

end Viterbo.Cap.PartC
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartC
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
lemma integral_inner_fourier_smul (m l : ℤ) (x y : Vector κ) :
    ∫ t : Time, inner (𝕜 := ℝ) (fourier m t • x) (fourier l t • y) ∂μ =
      if m = l then inner (𝕜 := ℝ) x y else 0 := by
  have hpt : ∀ t : Time, inner (𝕜 := ℝ) (fourier m t • x) (fourier l t • y) =
      RCLike.re ((starRingEnd ℂ) (fourier m t) * fourier l t * inner ℂ x y) := by
    intro t
    rw [real_inner_eq_complex_re, inner_smul_left, inner_smul_right]
    ring_nf
  simp_rw [hpt]
  have hint : Integrable (fun t : Time => (starRingEnd ℂ) (fourier m t) * fourier l t *
      inner ℂ x y) μ :=
    integrable_continuous (by fun_prop)
  rw [integral_re hint, integral_mul_const, integral_conj_fourier_mul]
  split_ifs
  · simp [real_inner_eq_complex_re]
  · simp

lemma integral_inner_sums {ι : Type} [Fintype ι] (S : Finset ℤ) (x : ℤ → Vector κ)
    (k : ι → ℤ) (y : ι → Vector κ) :
    ∫ t : Time, inner (𝕜 := ℝ) (∑ m ∈ S, fourier m t • x m) (∑ q, fourier (k q) t • y q) ∂μ =
      ∑ q, if k q ∈ S then inner (𝕜 := ℝ) (x (k q)) (y q) else 0 := by
  classical
  simp_rw [sum_inner, inner_sum]
  have hc : ∀ m q, Continuous fun t : Time =>
      inner (𝕜 := ℝ) (fourier m t • x m) (fourier (k q) t • y q) := fun m q =>
    ((fourier m).continuous.smul continuous_const).inner
      ((fourier (k q)).continuous.smul continuous_const)
  rw [integral_finsetSum _ (fun m _ => integrable_continuous
    (continuous_finsetSum _ fun q _ => hc m q))]
  have h2 : ∀ m, ∫ t : Time, ∑ q, inner (𝕜 := ℝ) (fourier m t • x m) (fourier (k q) t • y q) ∂μ
      = ∑ q, if m = k q then inner (𝕜 := ℝ) (x m) (y q) else 0 := by
    intro m
    rw [integral_finsetSum _ (fun q _ => integrable_continuous (hc m q))]
    simp_rw [integral_inner_fourier_smul]
  simp_rw [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq']

omit [Fintype κ] in
lemma neg_I_trigVel (D : ℕ) (b : ℤ → Vector κ) (t : ℝ) :
    -(Complex.I • trigVel D b t) =
      ∑ m ∈ Finset.Icc (-(D : ℤ)) D, fourier m (t : Time) • ((2 * Real.pi * m : ℝ) • b m) := by
  unfold trigVel
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fourier_coe_apply, ← Complex.coe_smul, smul_smul, smul_smul, ← neg_smul]
  congr 1
  push_cast
  simp only [div_one]
  linear_combination (-(2 * Real.pi * m * Complex.exp (2 * Real.pi * Complex.I * m * t))) *
    Complex.I_sq

lemma continuous_trigVel (D : ℕ) (b : ℤ → Vector κ) : Continuous (trigVel D b) := by
  unfold trigVel; fun_prop

lemma intervalIntegral_eq_average' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Time → E) : (∫ t in (0:ℝ)..1, f (t : Time)) = ∫ t : Time, f t ∂μ :=
  intervalIntegral_eq_average f

lemma continuous_coe_time : Continuous (fun t : ℝ => (t : Time)) :=
  AddCircle.continuous_mk' 1

/-! ## Reindexing and coefficients -/
lemma sum_Icc_sym {E : Type} [AddCommMonoid E] (D : ℕ) (g : ℤ → E) :
    ∑ m ∈ Finset.Icc (-(D : ℤ)) D, g m =
      g 0 + ∑ k ∈ Finset.range D, (g ((k + 1 : ℕ) : ℤ) + g (-((k + 1 : ℕ) : ℤ))) := by
  induction D with
  | zero => simp
  | succ D ih =>
    have hs : Finset.Icc (-((D + 1 : ℕ) : ℤ)) ((D + 1 : ℕ) : ℤ) =
        insert (-((D + 1 : ℕ) : ℤ)) (insert ((D + 1 : ℕ) : ℤ) (Finset.Icc (-(D : ℤ)) D)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hs, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; push_cast; omega), ih,
      Finset.sum_range_succ]
    abel

/-- Positive part of `b`, indexed by `ℕ`. -/
def bpos (D : ℕ) (b : ℤ → Vector κ) (m : ℕ) : Vector κ :=
  if 1 ≤ m ∧ m ≤ D then b m else 0

/-- `A₊ = π ∑_{1 ≤ m ≤ D} m ‖b m‖²`. -/
def Apos (D : ℕ) (b : ℤ → Vector κ) : ℝ :=
  Real.pi * ∑ k ∈ Finset.range D, ((k + 1 : ℕ) : ℝ) * ‖b ((k + 1 : ℕ) : ℤ)‖ ^ 2

/-- `δ = π ∑_{1 ≤ m ≤ D} m ‖b (-m)‖²`. -/
def Aneg (D : ℕ) (b : ℤ → Vector κ) : ℝ :=
  Real.pi * ∑ k ∈ Finset.range D, ((k + 1 : ℕ) : ℝ) * ‖b (-((k + 1 : ℕ) : ℤ))‖ ^ 2

lemma Aneg_nonneg (D : ℕ) (b : ℤ → Vector κ) : 0 ≤ Aneg D b := by
  unfold Aneg; positivity

lemma trigAction_eq' (D : ℕ) (b : ℤ → Vector κ) : trigAction D b = Apos D b - Aneg D b := by
  unfold trigAction Apos Aneg
  rw [sum_Icc_sym D (fun m => (m : ℝ) * ‖b m‖ ^ 2)]
  simp only [Int.cast_zero, zero_mul, zero_add, Finset.sum_add_distrib, Int.cast_neg,
    Int.cast_natCast, neg_mul, Finset.sum_neg_distrib]
  ring

lemma sum_fin_succ_le (N D : ℕ) (h : D ≤ N + 1) (F : ℕ → ℝ) :
    ∑ i : Fin (N + 1), (if (i : ℕ) + 1 ≤ D then F ((i : ℕ) + 1) else 0) =
      ∑ k ∈ Finset.range D, F (k + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 ≤ D then F (i + 1) else 0),
    ← Finset.sum_range_add_sum_Ico _ h]
  rw [Finset.sum_congr rfl (fun k hk => if_pos (by simp at hk; omega)),
    Finset.sum_congr rfl (fun k hk => if_neg (by simp at hk; omega))]
  simp

lemma sum_fin_le (N D : ℕ) (h : D ≤ N) (G : ℕ → ℝ) :
    ∑ i : Fin (N + 1), (if (i : ℕ) ≤ D then G i else 0) =
      G 0 + ∑ k ∈ Finset.range D, G (k + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ D then G i else 0),
    ← Finset.sum_range_add_sum_Ico _ (by omega : D + 1 ≤ N + 1)]
  rw [Finset.sum_congr rfl (fun k hk => if_pos (by simp at hk; omega)),
    Finset.sum_congr rfl (fun k hk => if_neg (by simp at hk; omega))]
  simp [Finset.sum_range_succ', add_comm]

omit [Fintype κ] in
lemma mode_joinCoeff_inl {ι ν : Type} (a : Coeff ι κ) (q : Coeff ν κ) (i : ι) :
    mode (joinCoeff a q) (Sum.inl i) = mode a i := by ext j; simp

omit [Fintype κ] in
lemma mode_joinCoeff_inr {ι ν : Type} (a : Coeff ι κ) (q : Coeff ν κ) (i : ν) :
    mode (joinCoeff a q) (Sum.inr i) = mode q i := by ext j; simp

omit [Fintype κ] in
lemma mode_smul {ι : Type} (s : ℝ) (q : Coeff ι κ) (i : ι) :
    mode (s • q) i = s • mode q i := by ext j; simp

omit [Fintype κ] in
lemma mode_posCoeff (f : ℕ → Vector κ) (N : ℕ) (i : Fin (N + 1)) :
    mode (posCoeff f N) i = f ((i : ℕ) + 1) := by ext j; simp [posCoeff]

lemma energy_mode {ι : Type} [Fintype ι] (w : ι → ℝ) (a : Coeff ι κ) :
    DiagonalQuadratic.energy (fun q : ι × κ => w q.1) a = ∑ i, w i * ‖mode a i‖ ^ 2 := by
  simp only [DiagonalQuadratic.energy, Fintype.sum_prod_type, EuclideanSpace.norm_sq_eq,
    mode_apply, Finset.mul_sum]

lemma norm_sq_mode {ι : Type} [Fintype ι] (a : Coeff ι κ) :
    ‖a‖ ^ 2 = ∑ i, ‖mode a i‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, mode_apply]

end Viterbo.Cap.PartC
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartC
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## The cone point -/
local instance instFactOneC2 : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

end Viterbo.Cap.PartC
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartC
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
/-- `A_y = π ∑ i ‖a_i‖²` (the negative-mode action). -/
def Ay {N : ℕ} (a : Coeff (Fin (N + 1)) κ) : ℝ :=
  ∑ i : Fin (N + 1), Real.pi * (i : ℕ) * ‖mode a i‖ ^ 2

lemma Ay_nonneg {N : ℕ} (a : Coeff (Fin (N + 1)) κ) : 0 ≤ Ay a := by
  unfold Ay; positivity

/-- The cross term `v = π ∑_{m<0} m Re⟨b_m, a_{-m}⟩`. -/
def vterm (D : ℕ) (b : ℤ → Vector κ) {N : ℕ} (a : Coeff (Fin (N + 1)) κ) : ℝ :=
  ∑ i : Fin (N + 1), if (i : ℕ) ≤ D then
    -(Real.pi * (i : ℕ)) * inner (𝕜 := ℝ) (b (-((i : ℕ) : ℤ))) (mode a i) else 0

omit [Fintype κ] in
lemma mode_bpos (D : ℕ) (b : ℤ → Vector κ) (N : ℕ) (i : Fin (N + 1)) :
    mode (posCoeff (bpos D b) N) i =
      if (i : ℕ) + 1 ≤ D then b (((i : ℕ) + 1 : ℕ) : ℤ) else 0 := by
  rw [mode_posCoeff]; unfold bpos
  by_cases h : (i : ℕ) + 1 ≤ D
  · rw [if_pos ⟨by omega, h⟩, if_pos h]
  · rw [if_neg (by omega), if_neg h]

lemma energy_cone (D : ℕ) (b : ℤ → Vector κ) {N : ℕ} (hN : D ≤ N)
    (a : Coeff (Fin (N + 1)) κ) (s : ℝ) :
    DiagonalQuadratic.energy (fun q => Real.pi * (frequency N q.1 : ℝ))
      (joinCoeff a (s • posCoeff (bpos D b) N)) = -Ay a + s ^ 2 * Apos D b := by
  rw [energy_joinCoeff]
  rw [energy_mode (fun i => Real.pi * (frequency N (Sum.inl i) : ℝ)),
    energy_mode (fun i => Real.pi * (frequency N (Sum.inr i) : ℝ))]
  simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode, mode_smul,
    norm_smul, mode_bpos]
  have h1 : ∑ i : Fin (N + 1), Real.pi * ((-((i : ℕ) : ℤ) : ℤ) : ℝ) * ‖mode a i‖ ^ 2 = -Ay a := by
    unfold Ay; rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [h1]
  have h2 : ∀ i : Fin (N + 1), Real.pi * ((((i : ℕ) + 1 : ℕ) : ℤ) : ℝ) *
      (‖s‖ * ‖if (i : ℕ) + 1 ≤ D then b (((i : ℕ) + 1 : ℕ) : ℤ) else 0‖) ^ 2 =
      s ^ 2 * (if (i : ℕ) + 1 ≤ D then
        Real.pi * (((i : ℕ) + 1 : ℕ) : ℝ) * ‖b (((i : ℕ) + 1 : ℕ) : ℤ)‖ ^ 2 else 0) := by
    intro i
    split_ifs
    · rw [Real.norm_eq_abs, mul_pow, sq_abs]; push_cast; ring
    · simp
  simp_rw [h2]
  rw [← Finset.mul_sum, sum_fin_succ_le N D (by omega)
    (fun m => Real.pi * (m : ℝ) * ‖b (m : ℤ)‖ ^ 2)]
  unfold Apos
  rw [Finset.mul_sum (s := Finset.range D) (a := Real.pi)]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

lemma norm_sq_cone (D : ℕ) (b : ℤ → Vector κ) {N : ℕ}
    (a : Coeff (Fin (N + 1)) κ) (s : ℝ) :
    ‖joinCoeff a (s • posCoeff (bpos D b) N)‖ ^ 2 =
      ‖a‖ ^ 2 + s ^ 2 * ‖posCoeff (bpos D b) N‖ ^ 2 := by
  rw [norm_sq_mode, norm_sq_mode a, norm_sq_mode (posCoeff (bpos D b) N),
    Fintype.sum_sum_type, Finset.mul_sum]
  simp only [mode_joinCoeff_inl, mode_joinCoeff_inr, mode_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

lemma Apos_le (D : ℕ) (b : ℤ → Vector κ) {N : ℕ} (hN : D ≤ N) :
    Apos D b ≤ Real.pi * D * ‖posCoeff (bpos D b) N‖ ^ 2 := by
  rw [norm_sq_mode, Finset.mul_sum]
  have : Apos D b = ∑ i : Fin (N + 1), (if (i : ℕ) + 1 ≤ D then
      Real.pi * (((i : ℕ) + 1 : ℕ) : ℝ) * ‖b (((i : ℕ) + 1 : ℕ) : ℤ)‖ ^ 2 else 0) := by
    rw [sum_fin_succ_le N D (by omega) (fun m => Real.pi * (m : ℝ) * ‖b (m : ℤ)‖ ^ 2)]
    unfold Apos; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [this]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mode_bpos]
  split_ifs with h
  · have : ((((i : ℕ) + 1 : ℕ)) : ℝ) ≤ D := by exact_mod_cast h
    have := Real.pi_pos
    gcongr
  · simp

lemma integral_cross (D : ℕ) (b : ℤ → Vector κ) {N : ℕ} (hN : D ≤ N)
    (a : Coeff (Fin (N + 1)) κ) (s : ℝ) :
    ∫ τ : Time, inner (𝕜 := ℝ)
      (∑ m ∈ Finset.Icc (-(D : ℤ)) D, fourier m τ • ((2 * Real.pi * m : ℝ) • b m))
      (loop (frequency N) (joinCoeff a (s • posCoeff (bpos D b) N)) τ) ∂μ =
      2 * vterm D b a + 2 * s * Apos D b := by
  simp only [loop_apply]
  rw [integral_inner_sums, Fintype.sum_sum_type]
  simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode,
    mode_joinCoeff_inl, mode_joinCoeff_inr, mode_smul, mode_bpos, real_inner_smul_left,
    real_inner_smul_right]
  congr 1
  · unfold vterm; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) ≤ D
    · rw [if_pos (by simp only [Finset.mem_Icc]; omega), if_pos h]; push_cast; ring
    · rw [if_neg (by simp only [Finset.mem_Icc]; omega), if_neg h]; ring
  · have : Apos D b = ∑ i : Fin (N + 1), (if (i : ℕ) + 1 ≤ D then
        Real.pi * (((i : ℕ) + 1 : ℕ) : ℝ) * ‖b (((i : ℕ) + 1 : ℕ) : ℤ)‖ ^ 2 else 0) := by
      rw [sum_fin_succ_le N D (by omega) (fun m => Real.pi * (m : ℝ) * ‖b (m : ℤ)‖ ^ 2)]
      unfold Apos; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) + 1 ≤ D
    · rw [if_pos (by simp only [Finset.mem_Icc]; omega), if_pos h, if_pos h,
        real_inner_self_eq_norm_sq]
      push_cast; ring
    · rw [if_neg (by simp only [Finset.mem_Icc]; omega), if_neg h]; ring

lemma vterm_sq_le (D : ℕ) (b : ℤ → Vector κ) {N : ℕ} (hN : D ≤ N)
    (a : Coeff (Fin (N + 1)) κ) : vterm D b a ^ 2 ≤ Aneg D b * Ay a := by
  set f : Fin (N + 1) → ℝ := fun i => if (i : ℕ) ≤ D then
    Real.sqrt (Real.pi * (i : ℕ)) * ‖b (-((i : ℕ) : ℤ))‖ else 0
  set g : Fin (N + 1) → ℝ := fun i => Real.sqrt (Real.pi * (i : ℕ)) * ‖mode a i‖
  have hpi : ∀ i : Fin (N + 1), 0 ≤ Real.pi * (i : ℕ) := fun i => by positivity
  have h1 : |vterm D b a| ≤ ∑ i, f i * g i := by
    unfold vterm
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    simp only [f, g]
    split_ifs
    · rw [abs_mul, abs_neg, abs_of_nonneg (hpi i)]
      have e : Real.sqrt (Real.pi * (i : ℕ)) * ‖b (-((i : ℕ) : ℤ))‖ *
          (Real.sqrt (Real.pi * (i : ℕ)) * ‖mode a i‖) =
          Real.pi * (i : ℕ) * (‖b (-((i : ℕ) : ℤ))‖ * ‖mode a i‖) := by
        rw [show ∀ x y w : ℝ, x * y * (x * w) = (x * x) * (y * w) from fun _ _ _ => by ring,
          Real.mul_self_sqrt (hpi i)]
      rw [e]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (hpi i)
    · simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hf : ∑ i, f i ^ 2 = Aneg D b := by
    have : ∀ i : Fin (N + 1), f i ^ 2 = if (i : ℕ) ≤ D then
        Real.pi * (i : ℕ) * ‖b (-((i : ℕ) : ℤ))‖ ^ 2 else 0 := by
      intro i; simp only [f]; split_ifs
      · rw [mul_pow, Real.sq_sqrt (hpi i)]
      · simp
    simp_rw [this]
    rw [sum_fin_le N D hN (fun m => Real.pi * (m : ℝ) * ‖b (-(m : ℤ))‖ ^ 2)]
    unfold Aneg; rw [Finset.mul_sum]; simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hg : ∑ i, g i ^ 2 = Ay a := by
    unfold Ay; refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g]; rw [mul_pow, Real.sq_sqrt (hpi i)]
  rw [hf, hg] at h2
  have h0 : 0 ≤ ∑ i, f i * g i := (abs_nonneg _).trans h1
  calc vterm D b a ^ 2 = |vterm D b a| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ i, f i * g i) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ ≤ _ := h2

end Viterbo.Cap.PartC
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartC
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part C -/
local instance instFactOneC3 : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

end Viterbo.Cap.PartC
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartC
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ] [DecidableEq κ]
theorem coneHyp_of_lower {H : Vector κ → ℝ} (hHc : Continuous H) {L : Set (Vector κ)}
    (hLc : Convex ℝ L) (hLb : Bornology.IsBounded L) (h0 : (0 : Vector κ) ∈ interior L)
    {α C₀ : ℝ} (hα : 0 < α) (hlow : ∀ z, α * gauge L z ^ 2 - C₀ ≤ H z)
    {D : ℕ} {b : ℤ → Vector κ}
    (hW : ∫ t in (0 : ℝ)..1, supportFn L (-(Complex.I • trigVel D b t)) ^ 2 <
      4 * α * trigAction D b) :
    ConeHyp H := by
  have hne : L.Nonempty := ⟨0, interior_subset h0⟩
  obtain ⟨R, hR⟩ := hLb.exists_norm_le
  set R1 := max R 1 with hR1def
  have hR1 : ∀ x ∈ L, ‖x‖ ≤ R1 := fun x hx => (hR x hx).trans (le_max_left _ _)
  have hR1pos : 0 < R1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set nf : ℝ → Vector κ := fun t => -(Complex.I • trigVel D b t) with hnf
  set Lsq := ∫ t in (0 : ℝ)..1, supportFn L (nf t) ^ 2 with hLsqdef
  have hLsq : 0 ≤ Lsq := intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
  rw [trigAction_eq'] at hW
  set Ap := Apos D b with hApdef
  set δ := Aneg D b with hδdef
  have hδ : 0 ≤ δ := Aneg_nonneg D b
  have hT : δ < Ap := by
    by_contra hc; push Not at hc
    have : 4 * α * (Ap - δ) ≤ 0 := by
      have := mul_le_mul_of_nonneg_left (sub_nonpos.2 hc) (by linarith : (0 : ℝ) ≤ 4 * α)
      linarith
    linarith
  have hAp : 0 < Ap := lt_of_le_of_lt hδ hT
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · exfalso; rw [hApdef, h] at hAp; simp [Apos] at hAp
    · exact h
  set η := α - Lsq / (4 * (Ap - δ)) with hηdef
  have hη : 0 < η := by
    have : Lsq / (4 * (Ap - δ)) < α := by
      rw [div_lt_iff₀ (by linarith)]; linarith
    linarith
  set m0 := min 1 (Ap / (Real.pi * D)) with hm0
  have hm0pos : 0 < m0 := lt_min one_pos (by have := Real.pi_pos; positivity)
  refine ⟨bpos D b, D, C₀, η / R1 ^ 2 * m0, by positivity, ?_, ?_, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    have : Ap = 0 := by
      rw [hApdef]; unfold Apos
      rw [Finset.sum_eq_zero (fun k hk => ?_), mul_zero]
      have := hc (k + 1)
      unfold bpos at this
      rw [if_pos ⟨by omega, by simp at hk; omega⟩] at this
      rw [this]; simp
    linarith
  · intro m hm; unfold bpos; rw [if_neg (by omega)]
  · simp [bpos]
  intro N hN a s hs
  set p := posCoeff (bpos D b) N with hpdef
  set cc := joinCoeff a (s • p) with hccdef
  set z := loop (frequency N) cc with hzdef
  set X := ∫ τ : Time, gauge L (z τ) ^ 2 ∂μ with hXdef
  have hgc : Continuous (gauge L) := continuous_gauge hLc (mem_interior_iff_mem_nhds.1 h0)
  have hX0 : 0 ≤ X := integral_nonneg (fun _ => sq_nonneg _)
  -- energy
  have hE : FourierPolynomial.action (frequency N) H cc =
      (-Ay a + s ^ 2 * Ap) - potential (frequency N) H cc := by
    rw [← energy_cone D b hN a s]; rfl
  -- potential
  have hP : α * X - C₀ ≤ potential (frequency N) H cc := by
    have h1 : ∫ τ : Time, (α * gauge L (z τ) ^ 2 - C₀) ∂μ ≤ ∫ τ : Time, H (z τ) ∂μ :=
      integral_mono (integrable_continuous (by fun_prop)) (integrable_continuous (by fun_prop))
        (fun τ => hlow _)
    rw [integral_sub (integrable_continuous (by fun_prop)) (integrable_const _),
      integral_const_mul] at h1
    have hc : ∫ _ : Time, C₀ ∂μ = C₀ := by simp
    rw [hc] at h1
    show α * X - C₀ ≤ ∫ τ : Time, H (z τ) ∂μ
    linarith
  -- coercivity
  have hcoer : ‖cc‖ ^ 2 / R1 ^ 2 ≤ X := by
    rw [← integral_loop_norm_sq (frequency N) (frequency_injective N) cc, ← integral_div]
    refine integral_mono (integrable_continuous (by fun_prop))
      (integrable_continuous (by fun_prop)) (fun τ => ?_)
    rw [div_le_iff₀ (by positivity)]
    have := norm_le_mul_gauge hLb h0 hR1 (z τ)
    have h2 : ‖z τ‖ ^ 2 ≤ (R1 * gauge L (z τ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) this 2
    simpa [hzdef, mul_pow, mul_comm] using h2
  -- the cross integral
  set nT : Time → Vector κ := fun τ =>
    ∑ m ∈ Finset.Icc (-(D : ℤ)) D, fourier m τ • ((2 * Real.pi * m : ℝ) • b m) with hnT
  have hI : ∫ t in (0 : ℝ)..1, inner (𝕜 := ℝ) (nf t) (z t) = 2 * vterm D b a + 2 * s * Ap := by
    have : ∀ t : ℝ, inner (𝕜 := ℝ) (nf t) (z t) = inner (𝕜 := ℝ) (nT t) (z t) := by
      intro t; simp only [hnf, hnT, neg_I_trigVel]
    simp_rw [this]
    rw [intervalIntegral_eq_average' (fun τ => inner (𝕜 := ℝ) (nT τ) (z τ))]
    exact integral_cross D b hN a s
  have hCS : 0 ≤ vterm D b a + s * Ap → 4 * (vterm D b a + s * Ap) ^ 2 ≤ Lsq * X := by
    intro hw
    have hcz : Continuous fun t : ℝ => gauge L (z t) :=
      hgc.comp (z.continuous.comp continuous_coe_time)
    have hnfc : Continuous nf := ((continuous_trigVel D b).const_smul Complex.I).neg
    have hcn : Continuous fun t : ℝ => supportFn L (nf t) :=
      (continuous_supportFn hLb hne).comp
        (show Continuous nf from ((continuous_trigVel D b).const_smul Complex.I).neg)
    have hle : ∫ t in (0 : ℝ)..1, inner (𝕜 := ℝ) (nf t) (z t) ≤
        ∫ t in (0 : ℝ)..1, supportFn L (nf t) * gauge L (z t) := by
      refine intervalIntegral.integral_mono_on zero_le_one
        ((hnfc.inner (z.continuous.comp continuous_coe_time)).intervalIntegrable _ _)
        ((hcn.mul hcz).intervalIntegrable _ _) (fun t _ => ?_)
      rw [real_inner_comm, mul_comm]
      exact inner_le_gauge_mul hLb h0 _ _
    have hcs := cs_interval hcn hcz
    have hXi : ∫ t in (0 : ℝ)..1, gauge L (z t) ^ 2 = X :=
      intervalIntegral_eq_average' (fun τ => gauge L (z τ) ^ 2)
    rw [hXi, ← hLsqdef] at hcs
    rw [hI] at hle
    have h2 : (2 * vterm D b a + 2 * s * Ap) ^ 2 ≤
        (∫ t in (0 : ℝ)..1, supportFn L (nf t) * gauge L (z t)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hle 2
    have e : 4 * (vterm D b a + s * Ap) ^ 2 = (2 * vterm D b a + 2 * s * Ap) ^ 2 := by ring
    rw [e]
    exact h2.trans hcs
  have hv := vterm_sq_le D b hN a
  have hq := quad_main hT hδ (Ay_nonneg a) hs hv hX0 hLsq hCS
  -- assemble
  have hp : Ap / (Real.pi * D) ≤ ‖p‖ ^ 2 := by
    rw [div_le_iff₀ (by have := Real.pi_pos; positivity)]
    have := Apos_le D b hN
    linarith
  have hnorm : m0 * (‖a‖ ^ 2 + s ^ 2) ≤ ‖cc‖ ^ 2 := by
    rw [hccdef, norm_sq_cone]
    have h1 : m0 ≤ 1 := min_le_left _ _
    have h2 : m0 ≤ ‖p‖ ^ 2 := (min_le_right _ _).trans hp
    nlinarith [sq_nonneg s, sq_nonneg ‖a‖, mul_le_mul_of_nonneg_left h2 (sq_nonneg s)]
  have hfin : η / R1 ^ 2 * m0 * (‖a‖ ^ 2 + s ^ 2) ≤ η * X := by
    have h1 : η / R1 ^ 2 * m0 * (‖a‖ ^ 2 + s ^ 2) ≤ η / R1 ^ 2 * ‖cc‖ ^ 2 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    have h2 : η / R1 ^ 2 * ‖cc‖ ^ 2 = η * (‖cc‖ ^ 2 / R1 ^ 2) := by ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hcoer hη.le)
  have hηX : η * X = α * X - Lsq * X / (4 * (Ap - δ)) := by rw [hηdef]; ring
  rw [hE]
  linarith

end Viterbo.Cap.PartC
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ] [DecidableEq κ]
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

theorem solution : type_of% @Viterbo.Cap.PartC.coneHyp_of_lower := @Viterbo.Cap.PartC.coneHyp_of_lower
