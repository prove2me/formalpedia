-- Prove2me | solution 1 for Viterbo.Cap.orbit_const_of_slow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T17:54:45.149404+00:00
-- url     : https://prove2.me/submissions/cee8ce74-7eaf-45ae-8366-5940595da0af

import Mathlib
import Definitions.Def_OAIQWSP000
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq
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

 theorem inner_I_self (z : Vector κ) : inner (𝕜 := ℝ) z (Complex.I • z) = 0 := by
  rw [real_inner_eq_complex_re, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [pow_two]

 theorem inner_I_left (z w : Vector κ) :
    inner (𝕜 := ℝ) (Complex.I • z) w = -inner (𝕜 := ℝ) z (Complex.I • w) := by
  simp only [real_inner_eq_complex_re, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re]

 theorem zero_derivative_constant {E : Type u117} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℝ → E} (hx : ∀ t, HasDerivAt x 0 t) (s t : ℝ) : x s = x t := by
  exact is_const_of_deriv_eq_zero (fun t => (hx t).differentiableAt) (fun t => (hx t).deriv) s t

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

/-- The `K`-length `∫₀¹ h_K(-J ż)` of a loop. -/
noncomputable def ell (K : Set (Phase n)) (z : ℝ → Phase n) : ℝ :=
  ∫ t in (0 : ℝ)..1, sSup ((fun x => phaseInner x (-J (deriv z t))) '' K)

/-- Absolutely continuous (as in `IsGeneralizedClosedCharacteristic`). -/
def IsAC (z : ℝ → Phase n) : Prop :=
  ∃ v : ℝ → Phase n, LocallyIntegrable v volume ∧ ∀ a b, z b - z a = ∫ s in a..b, v s

/-! ## Helpers -/

lemma pI_comm (z w : Phase n) : phaseInner z w = phaseInner w z := by
  simp [phaseInner, real_inner_comm]

lemma pI_sub_left (x y w : Phase n) :
    phaseInner (x - y) w = phaseInner x w - phaseInner y w := by
  simp [phaseInner, inner_sub_left]; ring

lemma pI_sub_right (w x y : Phase n) :
    phaseInner w (x - y) = phaseInner w x - phaseInner w y := by
  simp [phaseInner, inner_sub_right]; ring

lemma pI_smul_left (c : ℝ) (x w : Phase n) :
    phaseInner (c • x) w = c * phaseInner x w := by
  simp [phaseInner, real_inner_smul_left]; ring

lemma pI_smul_right (c : ℝ) (w x : Phase n) :
    phaseInner w (c • x) = c * phaseInner w x := by
  simp [phaseInner, real_inner_smul_right]; ring

lemma pI_zero_right (x : Phase n) : phaseInner x 0 = 0 := by simp [phaseInner]

lemma pI_self (z : Phase n) : phaseInner z z = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simp [phaseInner]

lemma norm_sq_le_pI (u : Phase n) : ‖u‖ ^ 2 ≤ phaseInner u u := by
  rw [pI_self, Prod.norm_def]
  rcases max_cases ‖u.1‖ ‖u.2‖ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    nlinarith [sq_nonneg ‖u.1‖, sq_nonneg ‖u.2‖]

lemma J_smul (c : ℝ) (z : Phase n) : J (c • z) = c • J z := by
  simp [J]

lemma J_sub (x y : Phase n) : J (x - y) = J x - J y := by
  refine Prod.ext ?_ ?_ <;> simp [J]; abel

lemma J_neg (x : Phase n) : J (-x) = -J x := by
  refine Prod.ext ?_ ?_ <;> simp [J]

lemma J_J (x : Phase n) : J (J x) = -x := by
  refine Prod.ext ?_ ?_ <;> simp [J]

lemma J_eq_zero {z : Phase n} (h : J z = 0) : z = 0 := by
  simp only [J, Prod.mk_eq_zero, neg_eq_zero] at h
  exact Prod.ext h.2 h.1

lemma pI_J_J (x y : Phase n) : phaseInner (J x) (J y) = phaseInner x y := by
  simp [phaseInner, J]; ring

lemma norm_negJ (x : Phase n) : ‖-J x‖ = ‖x‖ := by
  rw [norm_neg]; simp [J, Prod.norm_def, max_comm]

lemma continuous_J : Continuous (J : Phase n → Phase n) := by
  show Continuous fun z : Phase n => ((-z.2, z.1) : Phase n)
  fun_prop

lemma abs_pI_le (x y : Phase n) : |phaseInner x y| ≤ 2 * ‖x‖ * ‖y‖ := by
  unfold phaseInner
  have h1 := abs_real_inner_le_norm x.1 y.1
  have h2 := abs_real_inner_le_norm x.2 y.2
  have a1 := norm_fst_le x
  have a2 := norm_snd_le x
  have b1 := norm_fst_le y
  have b2 := norm_snd_le y
  calc |inner ℝ x.1 y.1 + inner ℝ x.2 y.2| ≤ |inner ℝ x.1 y.1| + |inner ℝ x.2 y.2| := abs_add_le _ _
    _ ≤ ‖x.1‖ * ‖y.1‖ + ‖x.2‖ * ‖y.2‖ := add_le_add h1 h2
    _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by gcongr
    _ = 2 * ‖x‖ * ‖y‖ := by ring

/-- `phaseInner · w` as a continuous linear functional. -/
noncomputable def pIL (w : Phase n) : Phase n →L[ℝ] ℝ :=
  (innerSL ℝ w.1).comp (ContinuousLinearMap.fst ℝ (Position n) (Position n)) +
    (innerSL ℝ w.2).comp (ContinuousLinearMap.snd ℝ (Position n) (Position n))

lemma pIL_apply (w z : Phase n) : pIL w z = phaseInner z w := by
  simp [pIL, phaseInner, real_inner_comm]

lemma continuous_pI : Continuous (fun p : Phase n × Phase n => phaseInner p.1 p.2) := by
  unfold phaseInner; fun_prop

/-! ### Absolutely continuous loops -/

lemma ii_of_li {v : ℝ → Phase n} (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable v volume a b :=
  (hv.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

lemma eq_prim {γ v : ℝ → Phase n} (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) :
    γ = fun x => γ 0 + ∫ s in (0 : ℝ)..x, v s := by
  funext x; rw [← hf 0 x]; abel

lemma cont_of_ac {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) : Continuous γ := by
  rw [eq_prim hf]
  exact continuous_const.add (intervalIntegral.continuous_primitive (ii_of_li hv) 0)

lemma hasDeriv_ae {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) : ∀ᵐ x, HasDerivAt γ (v x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hv] with x hx
  rw [eq_prim hf]
  simpa using (hx 0).const_add (γ 0)

lemma deriv_ae {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) : ∀ᵐ x, deriv γ x = v x :=
  (hasDeriv_ae hv hf).mono fun _ hx => hx.deriv

lemma ii_pI {w v : ℝ → Phase n} (hw : Continuous w) (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable (fun t => phaseInner (w t) (v t)) volume a b := by
  obtain ⟨C, hC⟩ :=
    (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn hw.continuousOn
  have hvi : IntegrableOn v (uIcc a b) volume := hv.integrableOn_isCompact isCompact_uIcc
  have : IntegrableOn (fun t => phaseInner (w t) (v t)) (uIcc a b) volume := by
    refine Integrable.mono' (hvi.norm.const_mul (2 * C)) ?_ ?_
    · have hm : AEStronglyMeasurable (fun t => (w t, v t)) (volume.restrict (uIcc a b)) :=
        hw.aestronglyMeasurable.prodMk hvi.aestronglyMeasurable
      have h4 := continuous_pI.comp_aestronglyMeasurable hm
      simpa only [Function.comp_def] using h4
    · refine (ae_restrict_iff' measurableSet_uIcc).2 (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs]
      have hCt : 2 * ‖w t‖ ≤ 2 * C := by linarith [hC t ht]
      calc _ ≤ 2 * ‖w t‖ * ‖v t‖ := abs_pI_le _ _
        _ ≤ 2 * C * ‖v t‖ := mul_le_mul_of_nonneg_right hCt (norm_nonneg _)
  exact this.intervalIntegrable

lemma integral_pI_const {v : ℝ → Phase n} (hv : LocallyIntegrable v volume) (c : Phase n)
    (a b : ℝ) : ∫ t in a..b, phaseInner c (v t) = phaseInner c (∫ t in a..b, v t) := by
  have h : ∀ x, phaseInner c x = pIL c x := fun x => by rw [pIL_apply, pI_comm]
  simp only [h]
  exact (pIL c).intervalIntegral_comp_comm (ii_of_li hv a b)

lemma action_eq {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) :
    action γ = 1 / 2 * ∫ t in (0 : ℝ)..1, phaseInner (J (γ t)) (v t) := by
  unfold action; congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [deriv_ae hv hf] with t ht _
  rw [ht]

/-! ### Support functions -/

/-- The support function `h_K(w)`. -/
noncomputable def supp (K : Set (Phase n)) (w : Phase n) : ℝ :=
  sSup ((fun x => phaseInner x w) '' K)

lemma bdd_supp {S : Set (Phase n)} (hS : Bornology.IsBounded S) (u : Phase n) :
    BddAbove ((fun y => phaseInner y u) '' S) := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine ⟨2 * R * ‖u‖, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  calc phaseInner y u ≤ |phaseInner y u| := le_abs_self _
    _ ≤ 2 * ‖y‖ * ‖u‖ := abs_pI_le _ _
    _ ≤ 2 * R * ‖u‖ := by gcongr; exact hR y hy

lemma supp_eq {S : Set (Phase n)} (hS : Bornology.IsBounded S) {x u : Phase n}
    (hx : x ∈ closure S) (hu : u ∈ normalCone phaseInner S x) :
    supp S u = phaseInner x u := by
  have hne : S.Nonempty := closure_nonempty_iff.1 ⟨x, hx⟩
  apply le_antisymm
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    have := hu y hy
    rw [pI_sub_right, pI_comm u y, pI_comm u x] at this
    linarith
  · have hsub : S ⊆ {y | phaseInner y u ≤ supp S u} :=
      fun y hy => le_csSup (bdd_supp hS u) (mem_image_of_mem _ hy)
    have hcl : IsClosed {y | phaseInner y u ≤ supp S u} :=
      isClosed_le (continuous_pI.comp (continuous_id.prodMk continuous_const)) continuous_const
    exact hcl.closure_subset_iff.2 hsub hx

lemma supp_le_add {K : Set (Phase n)} (hK : Bornology.IsBounded K) (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (w w' : Phase n) :
    supp K w ≤ supp K w' + 2 * R * ‖w - w'‖ := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  have h1 : phaseInner x w' ≤ supp K w' := le_csSup (bdd_supp hK w') (mem_image_of_mem _ hx)
  have h2 : phaseInner x (w - w') ≤ 2 * R * ‖w - w'‖ :=
    (le_abs_self _).trans ((abs_pI_le _ _).trans (by gcongr; exact hR x hx))
  rw [pI_sub_right] at h2
  simp only
  linarith

lemma supp_zero {K : Set (Phase n)} (hne : K.Nonempty) : supp K 0 = 0 := by
  unfold supp
  simp only [pI_zero_right]
  rw [hne.image_const, csSup_singleton]

lemma ii_supp {K : Set (Phase n)} (hK : IsConvexDomain K) {v : ℝ → Phase n}
    (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable (fun t => supp K (-J (v t))) volume a b := by
  obtain ⟨R, hR⟩ := hK.1.exists_norm_le
  have hne : K.Nonempty := hK.2.2.mono interior_subset
  obtain ⟨k0, hk0⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg k0).trans (hR k0 hk0)
  have hlip : LipschitzWith (Real.toNNReal (2 * R)) (supp K) := by
    refine LipschitzWith.of_le_add_mul _ fun x y => ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    exact supp_le_add hK.1 ⟨k0, hk0⟩ hR x y
  have hbd : ∀ w, |supp K w| ≤ 2 * R * ‖w‖ := fun w => by
    have h1 := supp_le_add hK.1 ⟨k0, hk0⟩ hR w 0
    have h2 := supp_le_add hK.1 ⟨k0, hk0⟩ hR 0 w
    rw [supp_zero ⟨k0, hk0⟩, sub_zero] at h1
    rw [supp_zero ⟨k0, hk0⟩, zero_sub, norm_neg] at h2
    rw [abs_le]; constructor <;> linarith
  have hvi : IntegrableOn v (uIcc a b) volume := hv.integrableOn_isCompact isCompact_uIcc
  have : IntegrableOn (fun t => supp K (-J (v t))) (uIcc a b) volume := by
    refine Integrable.mono' (hvi.norm.const_mul (2 * R)) ?_ ?_
    · exact (hlip.continuous.comp continuous_J.neg).comp_aestronglyMeasurable
        hvi.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs]
      calc _ ≤ 2 * R * ‖-J (v t)‖ := hbd _
        _ = 2 * R * ‖v t‖ := by rw [norm_negJ]
  exact this.intervalIntegrable

lemma ell_eq {z v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) (K : Set (Phase n)) :
    ell K z = ∫ t in (0 : ℝ)..1, supp K (-J (v t)) := by
  unfold ell
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [deriv_ae hv hf] with t ht _
  rw [ht]; rfl

/-! ### Translation -/

/-! ### Scaling -/

lemma normalCone_smul {S : Set (Phase n)} {α : ℝ} (hα : 0 < α) {x u : Phase n}
    (hu : u ∈ normalCone phaseInner S x) :
    α • u ∈ normalCone phaseInner (α • S) (α • x) := by
  rintro _ ⟨y, hy, rfl⟩
  have := hu y hy
  rw [← smul_sub, pI_smul_left, pI_smul_right]
  have h2 : 0 ≤ α * α := by positivity
  nlinarith

lemma frontier_smul' (S : Set (Phase n)) {α : ℝ} (hα : α ≠ 0) :
    frontier (α • S) = α • frontier S := by
  rw [← Set.image_smul, ← Set.image_smul]
  exact ((Homeomorph.smulOfNeZero α hα).image_frontier S).symm

lemma ftc_smul {γ v : ℝ → Phase n} (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) (α : ℝ) :
    ∀ a b, (fun t => α • γ t) b - (fun t => α • γ t) a = ∫ s in a..b, α • v s := by
  intro a b
  rw [intervalIntegral.integral_smul, ← hf a b, smul_sub]

lemma gcc_smul {S : Set (Phase n)} {γ : ℝ → Phase n} (h : IsGeneralizedClosedCharacteristic S γ)
    {α : ℝ} (hα : 0 < α) :
    IsGeneralizedClosedCharacteristic (α • S) (fun t => α • γ t) := by
  obtain ⟨hper, hfr, v, hvint, hftc, hae⟩ := h
  refine ⟨fun t => by simp only [hper t], fun t => ?_, fun t => α • v t, hvint.smul α,
    ftc_smul hftc α, ?_⟩
  · rw [frontier_smul' S hα.ne']; exact smul_mem_smul_set (hfr t)
  · filter_upwards [hae] with t ⟨u, hu, hvu⟩
    exact ⟨α • u, normalCone_smul hα hu, by rw [J_smul, hvu]⟩

lemma action_smul {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) (α : ℝ) :
    action (fun t => α • γ t) = α ^ 2 * action γ := by
  rw [action_eq (hv.smul α) (ftc_smul hf α), action_eq hv hf]
  have e : ∀ t, phaseInner (J (α • γ t)) (α • v t) = α ^ 2 * phaseInner (J (γ t)) (v t) := by
    intro t; rw [J_smul, pI_smul_left, pI_smul_right]; ring
  simp only [Pi.smul_apply, e, intervalIntegral.integral_const_mul]
  ring

lemma cEHZ_smul_le (S : Set (Phase n)) {α : ℝ} (hα : 0 < α) :
    cEHZ (α • S) ≤ ENNReal.ofReal (α ^ 2) * cEHZ S := by
  have h0 : ENNReal.ofReal (α ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  unfold cEHZ
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hγ => ?_
  have hnc : ∃ s t, (fun t => α • γ t) s ≠ (fun t => α • γ t) t := by
    obtain ⟨s, t, hst⟩ := hγ.2
    exact ⟨s, t, fun h => hst (smul_right_injective (Phase n) hα.ne' h)⟩
  refine (iInf₂_le (fun t => α • γ t) ⟨gcc_smul hγ.1 hα, hnc⟩).trans (le_of_eq ?_)
  obtain ⟨-, -, v, hv, hf, -⟩ := hγ.1
  rw [action_smul hv hf, abs_mul, abs_of_nonneg (sq_nonneg α),
    ENNReal.ofReal_mul (sq_nonneg α)]

/-! ### Positivity of the action -/

lemma cone_lower {S : Set (Phase n)} {x0 : Phase n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x0 r ⊆ S) {y u : Phase n} (hu : u ∈ normalCone phaseInner S y) :
    r / 2 * ‖u‖ ≤ phaseInner (y - x0) u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [pI_zero_right]
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set s := r / (2 * ‖u‖) with hs
  have hs0 : 0 < s := by positivity
  have hsu : s * ‖u‖ = r / 2 := by rw [hs]; field_simp
  have hz : x0 + s • u ∈ S := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0, hsu]
    linarith)
  have h1 := hu _ hz
  have h2 := norm_sq_le_pI u
  have e : phaseInner u (x0 + s • u - y) = s * phaseInner u u - phaseInner (y - x0) u := by
    rw [show x0 + s • u - y = s • u - (y - x0) by abel, pI_sub_right, pI_smul_right,
      pI_comm u (y - x0)]
  rw [e] at h1
  have : r / 2 * ‖u‖ = s * ‖u‖ ^ 2 := by rw [← hsu]; ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left h2 hs0.le]

lemma cEHZ_smul (S : Set (Phase n)) {α : ℝ} (hα : 0 < α) :
    cEHZ (α • S) = ENNReal.ofReal (α ^ 2) * cEHZ S := by
  refine le_antisymm (cEHZ_smul_le S hα) ?_
  have h2 := cEHZ_smul_le (α • S) (inv_pos.mpr hα)
  rw [inv_smul_smul₀ hα.ne'] at h2
  calc ENNReal.ofReal (α ^ 2) * cEHZ S
      ≤ ENNReal.ofReal (α ^ 2) * (ENNReal.ofReal (α⁻¹ ^ 2) * cEHZ (α • S)) := by gcongr
    _ = ENNReal.ofReal (α ^ 2 * α⁻¹ ^ 2) * cEHZ (α • S) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ = cEHZ (α • S) := by
        rw [← mul_pow, mul_inv_cancel₀ hα.ne', one_pow, ENNReal.ofReal_one, one_mul]

lemma isAC_of_char {S : Set (Phase n)} {γ : ℝ → Phase n}
    (hγ : IsGeneralizedClosedCharacteristic S γ) : IsAC γ := by
  obtain ⟨-, -, v, hv, hf, -⟩ := hγ
  exact ⟨v, hv, hf⟩

lemma ell_char {S : Set (Phase n)} (hS : IsConvexDomain S) {γ : ℝ → Phase n}
    (hγ : IsGeneralizedClosedCharacteristic S γ) : ell S γ = 2 * action γ := by
  obtain ⟨hper, hfr, v, hv, hf, hae⟩ := hγ
  rw [action_eq hv hf, ell_eq hv hf,
    show ∀ x : ℝ, 2 * (1 / 2 * x) = x from fun x => by ring]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae] with t ⟨u, hu, hvu⟩ _
  rw [← hvu, J_J, neg_neg, supp_eq hS.1 (frontier_subset_closure (hfr t)) hu, pI_J_J]

lemma action_pos_of_char {S : Set (Phase n)} (hS : IsConvexDomain S) {γ : ℝ → Phase n}
    (hγ : IsGeneralizedClosedCharacteristic S γ) (hnc : ∃ s t, γ s ≠ γ t) : 0 < action γ := by
  obtain ⟨hper, hfr, v, hv, hf, hae⟩ := hγ
  obtain ⟨x0, hx0⟩ := hS.2.2
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx0)
  have hγc := cont_of_ac hv hf
  set f : ℝ → ℝ := fun t => phaseInner (J (γ t - x0)) (v t) with hfdef
  have hfi : IntervalIntegrable f volume 0 1 :=
    ii_pI (continuous_J.comp (hγc.sub continuous_const)) hv 0 1
  have h2A : 2 * action γ = ∫ t in (0 : ℝ)..1, f t := by
    rw [action_eq hv hf]
    have e : ∀ t, f t = phaseInner (J (γ t)) (v t) - phaseInner (J x0) (v t) := fun t => by
      simp only [f, J_sub, pI_sub_left]
    simp only [e]
    rw [intervalIntegral.integral_sub (ii_pI (w := fun t => J (γ t)) (continuous_J.comp hγc) hv 0 1)
      (ii_pI (w := fun _ => J x0) continuous_const hv 0 1), integral_pI_const hv, ← hf 0 1,
      show γ 1 = γ 0 by simpa using hper 0, sub_self, pI_zero_right]
    ring
  have hpos : ∀ᵐ t, r / 2 * ‖-J (v t)‖ ≤ f t := by
    filter_upwards [hae] with t ⟨u, hu, hvu⟩
    have := cone_lower hr hball hu
    simp only [f]
    rw [← hvu, J_J, neg_neg, pI_J_J]
    exact this
  have hnn : ∀ᵐ t, 0 ≤ f t := hpos.mono fun t ht => le_trans (by positivity) ht
  by_contra hA
  push Not at hA
  have hint0 : ∫ t in (0 : ℝ)..1, f t = 0 := by
    have := intervalIntegral.integral_nonneg_of_ae zero_le_one hnn
    linarith
  have hf0 := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hnn) hfi).1
    hint0
  have hv0 : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1 ∪ Ioc 1 0)), v t = 0 := by
    filter_upwards [hf0, ae_restrict_of_ae hpos] with t h1 h2
    have h3 : r / 2 * ‖-J (v t)‖ ≤ 0 := by simpa [h1] using h2
    have h4 : ‖-J (v t)‖ ≤ 0 := by
      by_contra h5; push Not at h5
      have : 0 < r / 2 * ‖-J (v t)‖ := by positivity
      linarith
    have h6 : -J (v t) = 0 := norm_le_zero_iff.1 h4
    exact J_eq_zero (neg_eq_zero.1 h6)
  have hv0' := (ae_restrict_iff' (measurableSet_Ioc.union measurableSet_Ioc)).1 hv0
  have hconst : ∀ s, γ s = γ 0 := by
    intro s
    have hfs := Int.fract_nonneg s
    have hfs1 := Int.fract_lt_one s
    have hper' : γ (Int.fract s) = γ s := by
      rw [← Int.self_sub_floor]
      simpa using hper.sub_int_mul_eq (x := s) ⌊s⌋
    rw [← hper']
    have := hf 0 (Int.fract s)
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : Phase n)) ?_,
      intervalIntegral.integral_zero] at this
    · exact sub_eq_zero.1 this
    · filter_upwards [hv0'] with t ht ht'
      rw [Set.uIoc_of_le hfs] at ht'
      exact ht (Or.inl ⟨ht'.1, ht'.2.trans hfs1.le⟩)
  obtain ⟨s, t, hst⟩ := hnc
  exact hst (by rw [hconst s, hconst t])

lemma ell_nonneg {K : Set (Phase n)} (hK : IsConvexDomain K) {z : ℝ → Phase n}
    (hz : Function.Periodic z 1) (hac : IsAC z) : 0 ≤ ell K z := by
  obtain ⟨v, hv, hf⟩ := hac
  rw [ell_eq hv hf]
  obtain ⟨k0, hk0⟩ := hK.2.2.mono interior_subset
  have hlow : ∀ t, phaseInner (J k0) (v t) ≤ supp K (-J (v t)) := fun t => by
    have := le_csSup (bdd_supp hK.1 (-J (v t))) (mem_image_of_mem _ hk0)
    rw [show phaseInner k0 (-J (v t)) = phaseInner (J k0) (v t) by
      rw [← pI_J_J, J_neg, J_J, neg_neg]] at this
    exact this
  have h0 : ∫ t in (0 : ℝ)..1, phaseInner (J k0) (v t) = 0 := by
    rw [integral_pI_const hv, ← hf 0 1, show z 1 = z 0 by simpa using hz 0, sub_self,
      pI_zero_right]
  have hm := intervalIntegral.integral_mono_on zero_le_one
    (ii_pI (w := fun _ => J k0) continuous_const hv 0 1) (ii_supp hK hv 0 1) (fun t _ => hlow t)
  linarith

lemma ell_mono {K L : Set (Phase n)} (hK : IsConvexDomain K) (hL : IsConvexDomain L) (hKL : K ⊆ L)
    {z : ℝ → Phase n} (hac : IsAC z) : ell K z ≤ ell L z := by
  obtain ⟨v, hv, hf⟩ := hac
  rw [ell_eq hv hf, ell_eq hv hf]
  refine intervalIntegral.integral_mono_on zero_le_one (ii_supp hK hv 0 1) (ii_supp hL hv 0 1)
    (fun t _ => ?_)
  exact csSup_le_csSup (bdd_supp hL.1 _) ((hK.2.2.mono interior_subset).image _) (image_mono hKL)

/-- From Clarke's principle: the minimal action is attained, and positive. -/
theorem exists_char_cEHZ_eq (hn : 1 ≤ n) {S : Set (Phase n)} (hS : IsConvexDomain S) :
    ∃ γ : ℝ → Phase n, IsGeneralizedClosedCharacteristic S γ ∧ (∃ s t, γ s ≠ γ t) ∧
      0 < action γ ∧ cEHZ S = ENNReal.ofReal (action γ) ∧
      ∀ z : ℝ → Phase n, Function.Periodic z 1 → IsAC z → 0 < action z →
        4 * action γ * action z ≤ ell S z ^ 2 := by
  obtain ⟨γ, hγ, hnc, hkey⟩ :=
    exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq n hn S hS
  have hA := action_pos_of_char hS hγ hnc
  refine ⟨γ, hγ, hnc, hA, le_antisymm ?_ ?_, fun z hz hac hpos => hkey z hz hac hpos⟩
  · refine (iInf₂_le γ ⟨hγ, hnc⟩).trans ?_
    rw [abs_of_pos hA]
  · refine le_iInf₂ fun γ' hγ' => ?_
    have hA' := action_pos_of_char hS hγ'.1 hγ'.2
    rw [abs_of_pos hA']
    apply ENNReal.ofReal_le_ofReal
    have h1 : 4 * action γ * action γ' ≤ ell S γ' ^ 2 :=
      hkey γ' hγ'.1.1 (isAC_of_char hγ'.1) hA'
    rw [ell_char hS hγ'.1] at h1
    nlinarith

/-- Monotonicity of `cEHZ` under inclusion of convex domains. -/
theorem cEHZ_mono (hn : 1 ≤ n) {K L : Set (Phase n)} (hK : IsConvexDomain K) (hL : IsConvexDomain L)
    (hKL : K ⊆ L) : cEHZ K ≤ cEHZ L := by
  obtain ⟨γL, hγL, -, hAL, hcL, -⟩ := exists_char_cEHZ_eq hn hL
  obtain ⟨γK, -, -, hAK, hcK, hkeyK⟩ := exists_char_cEHZ_eq hn hK
  rw [hcK, hcL]
  apply ENNReal.ofReal_le_ofReal
  have h1 := hkeyK γL hγL.1 (isAC_of_char hγL) hAL
  have h2 := ell_nonneg hK hγL.1 (isAC_of_char hγL)
  have h3 := ell_mono hK hL hKL (isAC_of_char hγL)
  have h4 := ell_char hL hγL
  have h5 : ell K γL ^ 2 ≤ ell L γL ^ 2 := pow_le_pow_left₀ h2 h3 2
  rw [h4] at h5
  nlinarith

end Viterbo.CM
end

section
set_option autoImplicit false

open scoped ENNReal ContDiff Pointwise

namespace Viterbo.Capacities

open OAI.SymmetricPolar Set Topology

/-! ## Generic facts about symplectic embeddings -/

/-! ## The bridge `ℝ²ⁿ ≅ ℂⁿ`, `(q, p) ↦ q + i p` -/


theorem Φ_apply_apply {n : ℕ} (z : Phase n) (j : Fin n) :
    Φ n z j = (z.1 j : ℂ) + Complex.I * (z.2 j : ℂ) := rfl

theorem Ψ_apply_fst {n : ℕ} (w : OAI.FourierPolynomial.Vector (Fin n)) (j : Fin n) : (Ψ n w).1 j = (w j).re := rfl
theorem Ψ_apply_snd {n : ℕ} (w : OAI.FourierPolynomial.Vector (Fin n)) (j : Fin n) : (Ψ n w).2 j = (w j).im := rfl

theorem Φ_Ψ {n : ℕ} (w : OAI.FourierPolynomial.Vector (Fin n)) : Φ n (Ψ n w) = w := by
  ext j
  apply Complex.ext <;> simp [Φ_apply_apply, Ψ_apply_fst, Ψ_apply_snd]

theorem Ψ_Φ {n : ℕ} (z : Phase n) : Ψ n (Φ n z) = z := by
  ext j
  · simp [Φ_apply_apply, Ψ_apply_fst]
  · simp [Φ_apply_apply, Ψ_apply_snd]

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
/-! ### Helpers about the gauge -/
lemma body_nhds {r : ℝ} (hL : Body L r) : L ∈ 𝓝 (0 : Vector κ) :=
  Filter.mem_of_superset (Metric.ball_mem_nhds 0 hL.rpos) hL.ball

lemma body_absorbent {r : ℝ} (hL : Body L r) : Absorbent ℝ L :=
  absorbent_nhds_zero (body_nhds hL)

lemma body_continuous_gauge {r : ℝ} (hL : Body L r) : Continuous (gauge L) :=
  continuous_gauge hL.convex (body_nhds hL)

lemma body_gauge_le_norm {r : ℝ} (hL : Body L r) (x : Vector κ) : gauge L x ≤ ‖x‖ / r := by
  have h := gauge_mono (absorbent_ball_zero (𝕜 := ℝ) hL.rpos) hL.ball x
  rwa [gauge_ball hL.rpos.le] at h

lemma body_gauge_add_le {r : ℝ} (hL : Body L r) (x y : Vector κ) :
    gauge L (x + y) ≤ gauge L x + gauge L y :=
  gauge_add_le hL.convex (body_absorbent hL) x y

lemma body_gauge_sub_le {r : ℝ} (hL : Body L r) (z u : Vector κ) :
    gauge L (z - u) ≤ gauge L z + ‖u‖ / r := by
  calc gauge L (z - u) = gauge L (z + -u) := by rw [sub_eq_add_neg]
    _ ≤ gauge L z + gauge L (-u) := body_gauge_add_le hL _ _
    _ ≤ gauge L z + ‖u‖ / r := by
        have := body_gauge_le_norm hL (-u)
        rw [norm_neg] at this
        linarith

lemma body_convexOn_gauge {r : ℝ} (hL : Body L r) : ConvexOn ℝ univ (gauge L) :=
  ⟨convex_univ, fun x _ y _ a b ha hb _ => by
    calc gauge L (a • x + b • y) ≤ gauge L (a • x) + gauge L (b • y) :=
          body_gauge_add_le hL _ _
      _ = a • gauge L x + b • gauge L y := by
          rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb]⟩

lemma body_convexOn_gaugeSq {r : ℝ} (hL : Body L r) :
    ConvexOn ℝ univ (fun x => gauge L x ^ 2) :=
  (body_convexOn_gauge hL).pow (fun x _ => gauge_nonneg x) 2

/-! ### Helpers about the mollifier -/
lemma integrable_mul_normed {F : Vector κ → ℝ} (hF : Continuous F) :
    Integrable (fun u => F u * φ.normed volume u) volume :=
  (hF.mul φ.continuous_normed).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.mul_left (f := F))

lemma integral_const_mul_normed (c : ℝ) : ∫ u, c * φ.normed volume u = c := by
  rw [integral_const_mul, φ.integral_normed, mul_one]

lemma integrable_gaugeSq_sub {r : ℝ} (hL : Body L r) (z : Vector κ) :
    Integrable (fun u => gauge L (z - u) ^ 2 * φ.normed volume u) volume := by
  have hg := body_continuous_gauge hL
  exact integrable_mul_normed φ (by fun_prop)

lemma integrable_gaugeSq_add {r : ℝ} (hL : Body L r) (z : Vector κ) :
    Integrable (fun u => gauge L (z + u) ^ 2 * φ.normed volume u) volume := by
  have hg := body_continuous_gauge hL
  exact integrable_mul_normed φ (by fun_prop)

lemma mollQ_eq_add (z : Vector κ) :
    mollQ L φ z = ∫ u, gauge L (z + u) ^ 2 * φ.normed volume u := by
  unfold mollQ
  rw [← integral_neg_eq_self]
  simp [sub_neg_eq_add, φ.normed_neg]

/-- Directional derivative of a convex differentiable function is at most the increment. -/
lemma fderiv_le_of_convexOn {F : Vector κ → ℝ} (hc : ConvexOn ℝ univ F)
    (hd : Differentiable ℝ F) (z w : Vector κ) :
    fderiv ℝ F z w ≤ F (z + w) - F z := by
  let h : ℝ → ℝ := fun t => F (z + t • w)
  have hconv : ConvexOn ℝ univ h := ⟨convex_univ, fun s _ t _ a b ha hb hab => by
    have := hc.2 (mem_univ (z + s • w)) (mem_univ (z + t • w)) ha hb hab
    have e : z + (a • s + b • t) • w = a • (z + s • w) + b • (z + t • w) := by
      calc z + (a • s + b • t) • w = (a + b) • z + (a • s + b • t) • w := by
            rw [hab, one_smul]
        _ = a • (z + s • w) + b • (z + t • w) := by module
    simp only [h, e]
    exact this⟩
  have hi : HasDerivAt (fun t : ℝ => z + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
  have hD : HasDerivAt h (fderiv ℝ F z w) 0 :=
    (hd z).hasFDerivAt.comp_hasDerivAt_of_eq 0 hi (by simp)
  have := hconv.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hD
  simpa [slope_def_field, h] using this

lemma mollQ_smul_le {r : ℝ} (hL : Body L r) {t : ℝ} (ht : 1 ≤ t) (z : Vector κ) :
    mollQ L φ (t • z) ≤ t ^ 2 * mollQ L φ z := by
  have ht0 : 0 < t := by linarith
  set δ := t⁻¹ with hδ
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ ht
  have hδ0 : 0 ≤ δ := inv_nonneg.2 ht0.le
  have key : ∀ u, gauge L (t • z - u) ^ 2 * φ.normed volume u ≤
      t ^ 2 * (((1 + δ) / 2) * (gauge L (z - u) ^ 2 * φ.normed volume u) +
        ((1 - δ) / 2) * (gauge L (z + u) ^ 2 * φ.normed volume u)) := by
    intro u
    have e1 : t • z - u = t • (z - δ • u) := by
      rw [smul_sub, smul_smul, hδ, mul_inv_cancel₀ ht0.ne', one_smul]
    have e2 : z - δ • u = ((1 + δ) / 2) • (z - u) + ((1 - δ) / 2) • (z + u) := by module
    have hc := (body_convexOn_gaugeSq hL).2 (mem_univ (z - u)) (mem_univ (z + u))
      (by linarith : (0 : ℝ) ≤ (1 + δ) / 2) (by linarith : (0 : ℝ) ≤ (1 - δ) / 2) (by ring)
    rw [← e2] at hc
    simp only [smul_eq_mul] at hc
    rw [e1, gauge_smul_of_nonneg ht0.le, smul_eq_mul, mul_pow]
    have hρ := φ.nonneg_normed (μ := volume) u
    calc t ^ 2 * gauge L (z - δ • u) ^ 2 * φ.normed volume u
        ≤ t ^ 2 * ((1 + δ) / 2 * gauge L (z - u) ^ 2 + (1 - δ) / 2 * gauge L (z + u) ^ 2)
          * φ.normed volume u := by gcongr
      _ = _ := by ring
  calc mollQ L φ (t • z) ≤ ∫ u, t ^ 2 * (((1 + δ) / 2) * (gauge L (z - u) ^ 2 *
        φ.normed volume u) + ((1 - δ) / 2) * (gauge L (z + u) ^ 2 * φ.normed volume u)) := by
        refine integral_mono (integrable_gaugeSq_sub φ hL _) ?_ key
        exact (((integrable_gaugeSq_sub φ hL z).const_mul _).add
          ((integrable_gaugeSq_add φ hL z).const_mul _)).const_mul _
    _ = t ^ 2 * ((1 + δ) / 2 * mollQ L φ z + (1 - δ) / 2 * mollQ L φ z) := by
        rw [integral_const_mul, integral_add ((integrable_gaugeSq_sub φ hL z).const_mul _)
          ((integrable_gaugeSq_add φ hL z).const_mul _), integral_const_mul, integral_const_mul,
          ← mollQ_eq_add]
        rfl
    _ = t ^ 2 * mollQ L φ z := by ring

/-! ### The Part M lemmas -/
theorem contDiff_mollQ {r : ℝ} (hL : Body L r) : ContDiff ℝ ∞ (mollQ L φ) := by
  have e : mollQ L φ = convolution (φ.normed volume) (fun x => gauge L x ^ 2)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    ext z
    simp [mollQ, convolution_def, mul_comm]
  rw [e]
  exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
    ((body_continuous_gauge hL).pow 2).locallyIntegrable

end Viterbo.Cap.PartM
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
alias contDiff_mollQ := Viterbo.Cap.PartM.contDiff_mollQ

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem convexOn_mollQ {r : ℝ} (hL : Body L r) : ConvexOn ℝ univ (mollQ L φ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hx := integrable_gaugeSq_sub φ hL x
  have hy := integrable_gaugeSq_sub φ hL y
  rw [mollQ, mollQ, mollQ, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hx.const_mul a) (hy.const_mul b)]
  refine integral_mono (integrable_gaugeSq_sub φ hL _) ((hx.const_mul a).add (hy.const_mul b))
    fun u => ?_
  have hc := (body_convexOn_gaugeSq hL).2 (mem_univ (x - u)) (mem_univ (y - u)) ha hb hab
  have e : a • (x - u) + b • (y - u) = a • x + b • y - u := by
    calc a • (x - u) + b • (y - u) = a • x + b • y - (a + b) • u := by module
      _ = a • x + b • y - u := by rw [hab, one_smul]
  rw [e] at hc
  simp only [smul_eq_mul] at hc
  have hρ := φ.nonneg_normed (μ := volume) u
  calc gauge L (a • x + b • y - u) ^ 2 * φ.normed volume u
      ≤ (a * gauge L (x - u) ^ 2 + b * gauge L (y - u) ^ 2) * φ.normed volume u := by gcongr
    _ = _ := by ring

end Viterbo.Cap.PartM
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
alias convexOn_mollQ := Viterbo.Cap.PartM.convexOn_mollQ

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem gauge_sq_le_mollQ {r : ℝ} (hL : Body L r) (z : Vector κ) :
    gauge L z ^ 2 ≤ mollQ L φ z := by
  have h1 : gauge L z ^ 2 = ∫ u, gauge L z ^ 2 * φ.normed volume u :=
    (integral_const_mul_normed φ _).symm
  have hA := integrable_gaugeSq_sub φ hL z
  have hB := integrable_gaugeSq_add φ hL z
  have h2 : mollQ L φ z = ∫ u, (gauge L (z - u) ^ 2 * φ.normed volume u +
      gauge L (z + u) ^ 2 * φ.normed volume u) / 2 := by
    rw [integral_div, integral_add hA hB, ← mollQ_eq_add]
    unfold mollQ
    ring
  rw [h1, h2]
  refine integral_mono (φ.integrable_normed.const_mul _) ((hA.add hB).div_const 2) fun u => ?_
  have hρ := φ.nonneg_normed (μ := volume) u
  have h2z : gauge L ((2 : ℝ) • z) ≤ gauge L (z - u) + gauge L (z + u) := by
    have : (2 : ℝ) • z = (z - u) + (z + u) := by module
    rw [this]
    exact body_gauge_add_le hL _ _
  rw [gauge_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), smul_eq_mul] at h2z
  have hz0 := gauge_nonneg (s := L) z
  have hp : gauge L z ^ 2 ≤ (gauge L (z - u) ^ 2 + gauge L (z + u) ^ 2) / 2 := by
    nlinarith [sq_nonneg (gauge L (z - u) - gauge L (z + u))]
  calc gauge L z ^ 2 * φ.normed volume u
      ≤ (gauge L (z - u) ^ 2 + gauge L (z + u) ^ 2) / 2 * φ.normed volume u := by gcongr
    _ = _ := by ring

end Viterbo.Cap.PartM
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
alias gauge_sq_le_mollQ := Viterbo.Cap.PartM.gauge_sq_le_mollQ

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem mollQ_le {r : ℝ} (hL : Body L r) (z : Vector κ) :
    mollQ L φ z ≤ (gauge L z + φ.rOut / r) ^ 2 := by
  rw [← integral_const_mul_normed φ ((gauge L z + φ.rOut / r) ^ 2), mollQ]
  refine integral_mono (integrable_gaugeSq_sub φ hL z) (φ.integrable_normed.const_mul _)
    fun u => ?_
  by_cases hu : φ.normed volume u = 0
  · simp [hu]
  · have hu' : u ∈ Function.support (φ.normed volume) := hu
    rw [φ.support_normed_eq] at hu'
    have hu'' : ‖u‖ < φ.rOut := by simpa using hu'
    have hρ := φ.nonneg_normed (μ := volume) u
    have hg := body_gauge_sub_le hL z u
    have : ‖u‖ / r ≤ φ.rOut / r := by gcongr; exact hL.rpos.le
    have h0 := gauge_nonneg (s := L) (z - u)
    gcongr
    linarith

end Viterbo.Cap.PartM
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
alias mollQ_le := Viterbo.Cap.PartM.mollQ_le

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem inner_gradient_mollQ_le {r : ℝ} (hL : Body L r) (z : Vector κ) :
    inner (𝕜 := ℝ) (gradient (mollQ L φ) z) z ≤ 2 * mollQ L φ z := by
  have hd : Differentiable ℝ (mollQ L φ) := (contDiff_mollQ φ hL).differentiable (by simp)
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  have key : ∀ s : ℝ, 0 < s → fderiv ℝ (mollQ L φ) z z ≤ (2 + s) * mollQ L φ z := by
    intro s hs
    have h1 := fderiv_le_of_convexOn (convexOn_mollQ φ hL) hd z (s • z)
    rw [map_smul, smul_eq_mul, show z + s • z = (1 + s) • z by rw [add_smul, one_smul, add_comm]]
      at h1
    have h2 := mollQ_smul_le φ hL (t := 1 + s) (by linarith) z
    have h3 : s * fderiv ℝ (mollQ L φ) z z ≤ s * ((2 + s) * mollQ L φ z) := by
      calc s * fderiv ℝ (mollQ L φ) z z ≤ (1 + s) ^ 2 * mollQ L φ z - mollQ L φ z := by linarith
        _ = s * ((2 + s) * mollQ L φ z) := by ring
    exact le_of_mul_le_mul_left h3 hs
  have hc : Continuous (fun s : ℝ => (2 + s) * mollQ L φ z) := by fun_prop
  have ht : Tendsto (fun s : ℝ => (2 + s) * mollQ L φ z) (𝓝[>] 0) (𝓝 (2 * mollQ L φ z)) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => key s hs)

end Viterbo.Cap.PartM
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
alias inner_gradient_mollQ_le := Viterbo.Cap.PartM.inner_gradient_mollQ_le

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))

end Viterbo.Cap.PartM
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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))

end Viterbo.Cap.PartM
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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))

end Viterbo.Cap.PartM
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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))

end Viterbo.Cap.PartM
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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))

end Viterbo.Cap.PartM
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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))

end Viterbo.Cap.PartM
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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))

end Viterbo.Cap.PartM
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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))

end Viterbo.Cap.PartM
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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))

end Viterbo.Cap.PartM
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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartK
open Viterbo Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {n : ℕ}
/-!
# Part K: profiles of a mollified gauge on `K` have only constant `1`-periodic orbits

Route: the energy `Q(y t) = s` is constant; if `f'(s) = 0` the orbit is at rest. Otherwise the
orbit, transported by `Ψ`, is a nonconstant generalized closed characteristic of
`Ψ '' {Q ≤ s}` whose action lies in `[0, f'(s) s]`, while `{Q ≤ s} ⊇ μ K` with
`μ = √s - rOut/r`, so `cEHZ ≥ μ² cEHZ(Ψ '' K)`, contradicting `hslow`.
-/
/-! ## Transport helpers (copied from Part W) -/
/-- `Φ ∘ J = I • Φ`. -/
lemma Φ_J (z : Phase n) : Capacities.Φ n (J z) = Complex.I • Capacities.Φ n z := by
  ext j
  simp only [Capacities.Φ_apply_apply, J, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma inner_Φ (x y : Phase n) :
    inner (𝕜 := ℝ) (Capacities.Φ n x) (Capacities.Φ n y) = phaseInner x y := by
  simp only [phaseInner, real_inner_eq_re_inner, PiLp.inner_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Capacities.Φ_apply_apply, inner]

lemma J_Ψ (v : Vector (Fin n)) : J (Capacities.Ψ n v) = Capacities.Ψ n (Complex.I • v) := by
  rw [← Capacities.Ψ_Φ (J (Capacities.Ψ n v)), Φ_J, Capacities.Φ_Ψ]

lemma pI_Ψ (a b : Vector (Fin n)) :
    phaseInner (Capacities.Ψ n a) (Capacities.Ψ n b) = inner (𝕜 := ℝ) a b := by
  rw [← inner_Φ, Capacities.Φ_Ψ, Capacities.Φ_Ψ]

lemma inner_I_I {κ : Type} [Fintype κ] (a b : Vector κ) :
    inner (𝕜 := ℝ) (Complex.I • a) (Complex.I • b) = inner (𝕜 := ℝ) a b := by
  rw [OAI.HamiltonianODE.inner_I_left, smul_smul, Complex.I_mul_I, neg_one_smul, inner_neg_right,
    neg_neg]

/-! ## Calculus helpers -/
/-- The gradient inequality for a convex differentiable function. -/
lemma convex_grad_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Q : E → ℝ}
    (hc : ConvexOn ℝ univ Q) {x : E} {Q' : E →L[ℝ] ℝ} (hd : HasFDerivAt Q Q' x) (u : E) :
    Q' (u - x) ≤ Q u - Q x := by
  let ℓ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x u
  have hg : ConvexOn ℝ univ (Q ∘ ℓ) := by
    simpa using hc.comp_affineMap ℓ
  have hdx : HasDerivAt (Q ∘ ℓ) (Q' (u - x)) 0 := by
    have h1 : HasDerivAt ℓ (u - x) 0 := AffineMap.hasDerivAt_lineMap
    have h2 : HasFDerivAt Q Q' (ℓ 0) := by
      simpa [ℓ] using hd
    exact h2.comp_hasDerivAt 0 h1
  have := hg.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hdx
  rw [slope_def_field] at this
  simpa [ℓ] using this

lemma gradient_comp {κ : Type} [Fintype κ] {Q : Vector κ → ℝ} {f : ℝ → ℝ} {w : Vector κ}
    (hQ : DifferentiableAt ℝ Q w) (hf : DifferentiableAt ℝ f (Q w)) :
    gradient (fun w => f (Q w)) w = deriv f (Q w) • gradient Q w := by
  have h1 : HasFDerivAt (fun w => f (Q w)) (deriv f (Q w) • fderiv ℝ Q w) w :=
    hf.hasDerivAt.comp_hasFDerivAt w hQ.hasFDerivAt
  unfold gradient
  rw [h1.fderiv, LinearIsometryEquiv.map_smul]

lemma contDiff_gradient {κ : Type} [Fintype κ] {Q : Vector κ → ℝ} (hQ : ContDiff ℝ ∞ Q) :
    ContDiff ℝ 1 (gradient Q) := by
  have h : gradient Q = fun z => (InnerProductSpace.toDual ℝ (Vector κ)).symm (fderiv ℝ Q z) :=
    rfl
  rw [h]
  exact (InnerProductSpace.toDual ℝ (Vector κ)).symm.contDiff.comp
    (hQ.fderiv_right (m := 1) (by norm_cast))

/-! ## Part K -/
theorem orbit_const_of_slow {n : ℕ} (hn : 1 ≤ n) {K : Set (Vector (Fin n))} {r : ℝ}
    (hK : Body K r) (hKd : IsConvexDomain (Capacities.Ψ n '' K))
    (φ : ContDiffBump (0 : Vector (Fin n))) (hφ : φ.rOut < r)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hf0 : ∀ s, 0 ≤ deriv f s)
    (hfa : ∀ s, s ≤ (2 * φ.rOut / r) ^ 2 → deriv f s = 0)
    (hslow : ∀ s, 0 < deriv f s →
      deriv f s * s < (Real.sqrt s - φ.rOut / r) ^ 2 * (cEHZ (Capacities.Ψ n '' K)).toReal)
    {y : ℝ → Vector (Fin n)}
    (hy : ∀ t, HasDerivAt y (Complex.I • gradient (fun w => f (mollQ K φ w)) (y t)) t)
    (hp : y 1 = y 0) : ∀ t, y t = y 0 := by
  classical
  set Q := mollQ K φ with hQdef
  have hr := hK.rpos
  set c := φ.rOut / r with hcdef
  have hc0 : 0 < c := div_pos φ.rOut_pos hr
  have hQs : ContDiff ℝ ∞ Q := contDiff_mollQ φ hK
  have hQd : Differentiable ℝ Q := hQs.differentiable (by simp)
  have hQc : ConvexOn ℝ univ Q := convexOn_mollQ φ hK
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgrad : ∀ w, gradient (fun w => f (Q w)) w = deriv f (Q w) • gradient Q w :=
    fun w => gradient_comp (hQd w) (hfd _)
  have hQ0 : Q 0 ≤ c ^ 2 := by
    have := mollQ_le φ hK 0
    simpa [gauge_zero] using this
  have hgc : Continuous (gradient Q) := (contDiff_gradient hQs).continuous
  have hFD : ∀ x, HasFDerivAt Q (InnerProductSpace.toDual ℝ _ (gradient Q x)) x :=
    fun x => (hQd x).hasGradientAt.hasFDerivAt
  have hgl : ∀ x u, inner (𝕜 := ℝ) (gradient Q x) (u - x) ≤ Q u - Q x := by
    intro x u
    have := convex_grad_le hQc (hFD x) u
    simpa only [InnerProductSpace.toDual_apply_apply] using this
  -- the energy is constant
  have hE : ∀ t, Q (y t) = Q (y 0) := by
    intro t
    refine OAI.HamiltonianODE.zero_derivative_constant (x := Q ∘ y) (fun u => ?_) t 0
    have hh := (hFD (y u)).comp_hasDerivAt u (hy u)
    have key : inner (𝕜 := ℝ) (gradient Q (y u))
        (Complex.I • gradient (fun w => f (Q w)) (y u)) = 0 := by
      rw [hgrad, smul_comm, real_inner_smul_right, OAI.HamiltonianODE.inner_I_self, mul_zero]
    simpa only [InnerProductSpace.toDual_apply_apply, key] using hh
  set s := Q (y 0) with hsdef
  set lam := deriv f s with hlam
  have hy' : ∀ t, HasDerivAt y (lam • (Complex.I • gradient Q (y t))) t := by
    intro t
    have := hy t
    rw [hgrad, hE t, smul_comm] at this
    exact this
  by_contra hne
  push Not at hne
  obtain ⟨t₁, ht₁⟩ := hne
  have hlam0 : 0 < lam := by
    rcases (hf0 s).lt_or_eq with h | h
    · exact h
    · exfalso
      apply ht₁
      refine OAI.HamiltonianODE.zero_derivative_constant (fun t => ?_) t₁ 0
      have := hy' t
      have h0 : lam = 0 := h.symm
      rwa [h0, zero_smul] at this
  -- the level is high
  have hs2 : (2 * c) ^ 2 < s := by
    by_contra h
    push Not at h
    have := hfa s (by rw [mul_div_assoc]; exact h)
    linarith
  have hsc : c ^ 2 < s := by nlinarith
  have hs0 : 0 < s := by nlinarith
  have hsq : 2 * c < Real.sqrt s := (Real.lt_sqrt (by positivity)).2 hs2
  set μ := Real.sqrt s - c with hμdef
  have hμ : 0 < μ := by linarith
  have hμs : (μ + c) ^ 2 = s := by
    rw [hμdef, sub_add_cancel, Real.sq_sqrt hs0.le]
  -- the sublevel set
  obtain ⟨Ks, hKsdef⟩ : ∃ Ks : Set (Vector (Fin n)), Ks = {z | Q z ≤ s} := ⟨_, rfl⟩
  have hmem : ∀ z, z ∈ Ks ↔ Q z ≤ s := fun z => by rw [hKsdef]; rfl
  have hKs_conv : Convex ℝ Ks := by
    rw [hKsdef]
    simpa using hQc.convex_le s
  obtain ⟨R0, hR0⟩ := hK.bounded.subset_closedBall 0
  have habs : Absorbent ℝ K :=
    absorbent_nhds_zero (Filter.mem_of_superset (Metric.ball_mem_nhds 0 hr) hK.ball)
  set Rb := (Real.sqrt s + 1) * R0 with hRb
  have hKsub : Ks ⊆ Metric.closedBall 0 Rb := by
    intro z hz
    rw [hmem] at hz
    have hg2 : gauge K z ^ 2 ≤ s := (gauge_sq_le_mollQ φ hK z).trans hz
    have hg : gauge K z ≤ Real.sqrt s := by
      have := Real.sqrt_le_sqrt hg2
      rwa [Real.sqrt_sq (gauge_nonneg _)] at this
    obtain ⟨b, hb0, hb1, hbz⟩ := exists_lt_of_gauge_lt habs (show gauge K z < Real.sqrt s + 1 by
      linarith)
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hbz
    have hkR : ‖k‖ ≤ R0 := by simpa using hR0 hk
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
    have hk0 := norm_nonneg k
    have := Real.sqrt_nonneg s
    calc b * ‖k‖ ≤ (Real.sqrt s + 1) * ‖k‖ := by gcongr
      _ ≤ (Real.sqrt s + 1) * R0 := by gcongr
  have hKs_bdd : Bornology.IsBounded Ks := Metric.isBounded_closedBall.subset hKsub
  have hball : ∀ t, y t ∈ Metric.closedBall 0 Rb := fun t =>
    hKsub ((hmem _).2 (hE t).le)
  -- periodicity, by uniqueness for the autonomous ODE
  obtain ⟨Lc, hLip⟩ : ∃ Lc, LipschitzOnWith Lc
      (fun z => lam • (Complex.I • gradient Q z)) (Metric.closedBall (0 : Vector (Fin n)) Rb) := by
    refine ContDiffOn.exists_lipschitzOnWith (n := 1) ?_ one_ne_zero (convex_closedBall _ _)
      (isCompact_closedBall _ _)
    exact (((contDiff_gradient hQs).const_smul Complex.I).const_smul lam).contDiffOn
  have hper : ∀ t, y (t + 1) = y t := by
    have := ODE_solution_unique_univ (v := fun _ z => lam • (Complex.I • gradient Q z))
      (s := fun _ => Metric.closedBall 0 Rb) (K := Lc) (t₀ := 0) (f := fun t => y (t + 1))
      (g := y) (fun _ => hLip) (fun t => ⟨(hy' (t + 1)).comp_add_const t 1, hball _⟩)
      (fun t => ⟨hy' t, hball t⟩) (by simp [hp])
    intro t
    exact congrFun this t
  -- the level set lies on the frontier of `Ks`
  have hfront : ∀ z, Q z = s → z ∈ frontier Ks := by
    intro z hz
    rw [frontier, Set.mem_sdiff]
    refine ⟨subset_closure ((hmem z).2 hz.le), fun hint => ?_⟩
    have hT : Tendsto (fun t : ℝ => t • z) (𝓝[>] 1) (𝓝 z) := by
      have : Tendsto (fun t : ℝ => t • z) (𝓝 1) (𝓝 ((1 : ℝ) • z)) :=
        (continuous_id.smul continuous_const).tendsto 1
      rw [one_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev := (hT.eventually (isOpen_interior.mem_nhds hint)).and self_mem_nhdsWithin
    obtain ⟨t, ht, ht1⟩ := hev.exists
    have ht1' : (1 : ℝ) < t := ht1
    have hQt : Q (t • z) ≤ s := (hmem _).1 (interior_subset ht)
    have ht0 : 0 < t := by linarith
    have hcv := hQc.2 (mem_univ (t • z)) (mem_univ 0) (show (0 : ℝ) ≤ 1 / t by positivity)
      (show (0 : ℝ) ≤ 1 - 1 / t by rw [sub_nonneg, div_le_one ht0]; linarith)
      (show 1 / t + (1 - 1 / t) = (1 : ℝ) by ring)
    have hvec : (1 / t) • (t • z) + (1 - 1 / t) • (0 : Vector (Fin n)) = z := by
      rw [smul_smul, one_div, inv_mul_cancel₀ ht0.ne', one_smul, smul_zero, add_zero]
    rw [hvec, smul_eq_mul, smul_eq_mul, hz] at hcv
    have hpos : 0 < 1 - 1 / t := by
      rw [sub_pos, div_lt_one ht0]; exact ht1'
    have h1 : (1 / t) * Q (t • z) ≤ (1 / t) * s := by gcongr
    have h2 : (1 - 1 / t) * Q 0 ≤ (1 - 1 / t) * c ^ 2 := by gcongr
    nlinarith
  -- transport to phase space
  let E : Vector (Fin n) ≃L[ℝ] Phase n :=
    ContinuousLinearEquiv.equivOfInverse (Capacities.Ψ n) (Capacities.Φ n)
      (fun w => Capacities.Φ_Ψ w) (fun z => Capacities.Ψ_Φ z)
  have himg : ∀ A : Set (Vector (Fin n)), E.toHomeomorph '' A = Capacities.Ψ n '' A :=
    fun A => rfl
  set S := Capacities.Ψ n '' Ks with hSdef
  have hS : IsConvexDomain S := by
    refine ⟨(Capacities.Ψ n).lipschitz.isBounded_image hKs_bdd,
      hKs_conv.linear_image (Capacities.Ψ n : Vector (Fin n) →ₗ[ℝ] Phase n), ?_⟩
    have hopen : IsOpen {z : Vector (Fin n) | Q z < s} := isOpen_lt hQs.continuous continuous_const
    have hopen' : IsOpen (Capacities.Ψ n '' {z | Q z < s}) := by
      rw [← himg]; exact E.toHomeomorph.isOpenMap _ hopen
    refine ⟨Capacities.Ψ n 0, interior_maximal (image_mono fun z (hz : Q z < s) => (hmem z).2 hz.le) hopen'
      (mem_image_of_mem _ ?_)⟩
    show Q 0 < s
    linarith
  -- the characteristic
  set γ : ℝ → Phase n := fun t => Capacities.Ψ n (y t) with hγdef
  set v : ℝ → Phase n := fun t => Capacities.Ψ n (lam • (Complex.I • gradient Q (y t))) with hvdef
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy' t).continuousAt
  have hvc : Continuous v := by
    simp only [hvdef]
    have hcont : Continuous fun t => lam • (Complex.I • gradient Q (y t)) :=
      ((hgc.comp hyc).const_smul Complex.I).const_smul lam
    exact (Capacities.Ψ n).continuous.comp hcont
  have hγ' : ∀ t, HasDerivAt γ (v t) t := fun t =>
    (Capacities.Ψ n).hasFDerivAt.comp_hasDerivAt t (hy' t)
  have hftc : ∀ a b, γ b - γ a = ∫ u in a..b, v u := fun a b =>
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hγ' t)
      (hvc.intervalIntegrable a b)).symm
  have hgcc : IsGeneralizedClosedCharacteristic S γ := by
    refine ⟨fun t => by simp only [hγdef, hper], fun t => ?_, v, hvc.locallyIntegrable, hftc,
      Filter.Eventually.of_forall fun t => ?_⟩
    · rw [hSdef, ← himg, ← E.toHomeomorph.image_frontier, himg]
      exact mem_image_of_mem _ (hfront _ (hE t))
    · refine ⟨Capacities.Ψ n (lam • gradient Q (y t)), ?_, ?_⟩
      · rintro _ ⟨u, hu, rfl⟩
        rw [← map_sub, pI_Ψ, real_inner_smul_left]
        have h1 := hgl (y t) u
        have h2 : Q u ≤ s := (hmem u).1 hu
        have h3 := hE t
        exact mul_nonpos_of_nonneg_of_nonpos hlam0.le (by linarith)
      · rw [J_Ψ, smul_comm]
  have hnc : ∃ a b, γ a ≠ γ b := by
    refine ⟨t₁, 0, fun h => ht₁ ?_⟩
    have := congrArg (Capacities.Φ n) h
    simpa only [hγdef, Capacities.Φ_Ψ] using this
  -- its action
  set g : ℝ → ℝ := fun t => lam * inner (𝕜 := ℝ) (y t) (gradient Q (y t)) with hgdef
  have hpt : ∀ t, phaseInner (J (γ t)) (v t) = g t := by
    intro t
    simp only [hγdef, hvdef, hgdef]
    rw [J_Ψ, pI_Ψ, real_inner_smul_right, inner_I_I]
  have hA : action γ = 1 / 2 * ∫ t in (0 : ℝ)..1, g t := by
    rw [Viterbo.CM.action_eq hvc.locallyIntegrable hftc]
    congr 1
    exact intervalIntegral.integral_congr fun t _ => hpt t
  have hgcont : Continuous g := by
    simp only [hgdef]
    exact continuous_const.mul (hyc.inner (hgc.comp hyc))
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    have h1 := hgl (y t) 0
    rw [zero_sub, inner_neg_right, hE t] at h1
    simp only [hgdef]
    rw [real_inner_comm]
    exact mul_nonneg hlam0.le (by linarith)
  have hg1 : ∀ t, g t ≤ 2 * lam * s := by
    intro t
    have h1 : inner (𝕜 := ℝ) (gradient Q (y t)) (y t) ≤ 2 * Q (y t) :=
      inner_gradient_mollQ_le φ hK (y t)
    rw [hE t] at h1
    simp only [hgdef]
    rw [real_inner_comm]
    have := mul_le_mul_of_nonneg_left h1 hlam0.le
    linarith
  have hAle : |action γ| ≤ lam * s := by
    have hi0 : 0 ≤ ∫ t in (0 : ℝ)..1, g t :=
      intervalIntegral.integral_nonneg zero_le_one fun t _ => hg0 t
    have hi1 : ∫ t in (0 : ℝ)..1, g t ≤ ∫ t in (0 : ℝ)..1, (2 * lam * s) :=
      intervalIntegral.integral_mono_on zero_le_one (hgcont.intervalIntegrable 0 1)
        intervalIntegrable_const fun t _ => hg1 t
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hi1
    rw [hA, abs_of_nonneg (by positivity)]
    linarith
  have hup : cEHZ S ≤ ENNReal.ofReal (lam * s) := by
    unfold cEHZ
    exact (iInf₂_le γ ⟨hgcc, hnc⟩).trans (ENNReal.ofReal_le_ofReal hAle)
  -- the lower bound
  have hμK : μ • K ⊆ Ks := by
    intro z hz
    have hgz : gauge K z ≤ μ := gauge_le_of_mem hμ.le hz
    have h1 := mollQ_le φ hK z
    rw [hmem, ← hμs]
    refine h1.trans ?_
    have := gauge_nonneg (s := K) z
    gcongr
  have hdom : IsConvexDomain (μ • (Capacities.Ψ n '' K)) := by
    refine ⟨hKd.1.smul₀ μ, hKd.2.1.smul μ, ?_⟩
    rw [interior_smul₀ hμ.ne']
    exact hKd.2.2.smul_set
  have hsub : μ • (Capacities.Ψ n '' K) ⊆ S := by
    rw [← image_smul_set]
    exact image_mono hμK
  have hlow := Viterbo.CM.cEHZ_mono hn hdom hS hsub
  rw [Viterbo.CM.cEHZ_smul _ hμ] at hlow
  have hfin := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hlow.trans hup)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (by positivity)] at hfin
  have := hslow s hlam0
  linarith

end Viterbo.Cap.PartK
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

theorem solution : type_of% @Viterbo.Cap.PartK.orbit_const_of_slow := @Viterbo.Cap.PartK.orbit_const_of_slow
