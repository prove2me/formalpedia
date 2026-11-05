-- Prove2me | solution 1 for Viterbo.Cap.exists_trig_loop
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T17:54:43.585125+00:00
-- url     : https://prove2.me/submissions/1f16db44-217b-4d84-b694-a5f345292303

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartW
open Viterbo Viterbo.CM Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {n : ℕ}
/-!
# Part W: a trigonometric loop beating `α > c_EHZ(L)`

Route: Clarke's minimal characteristic `γ`; reparametrize by normalized `h_L`-arclength plus `ε t`
so that `h_L(-J(w b - w a)) ≤ (ℓ + ε)(b - a)`; smooth with the kernel `cos(π s)^{2M}` (a
nonnegative trigonometric polynomial) to get a trigonometric polynomial with the same bound on
`h_L(-J ẇ)`; the action converges by Riemann sums. The partition-sum tools are copied from
`Solutions/Viterbo/CLPartP.lean` (which sits on `CMBase`, clashing with `CMProof`).
-/
/-! ## Copied from the Clarke blueprint (Parts P and R) -/
/-- A loop: `1`-periodic and absolutely continuous. -/
def IsLoop (z : ℝ → Phase n) : Prop := Function.Periodic z 1 ∧ IsAC z

/-- A partition `0 = t₀ < t₁ < ⋯ < t_N = 1` of `[0, 1]`. -/
def IsPart {N : ℕ} (t : Fin (N + 1) → ℝ) : Prop :=
  t 0 = 0 ∧ t (Fin.last N) = 1 ∧ StrictMono t

/-- Mesh at most `δ`. -/
def MeshLE {N : ℕ} (t : Fin (N + 1) → ℝ) (δ : ℝ) : Prop :=
  ∀ i : Fin N, t i.succ - t i.castSucc ≤ δ

/-- Riemann sum of the action. -/
def rsum (z : ℝ → Phase n) {N : ℕ} (t : Fin (N + 1) → ℝ) : ℝ :=
  1 / 2 * ∑ i : Fin N, phaseInner (J (z (t i.castSucc))) (z (t i.succ) - z (t i.castSucc))

lemma pI_negJ (x y : Phase n) : phaseInner x (-J y) = phaseInner (J x) y := by
  rw [← pI_J_J, J_neg, J_J, neg_neg]

lemma norm_J (x : Phase n) : ‖J x‖ = ‖x‖ := by
  rw [← norm_neg, norm_negJ]

lemma supp_smul (K : Set (Phase n)) {c : ℝ} (hc : 0 ≤ c) (u : Phase n) :
    supp K (c • u) = c * supp K u := by
  unfold supp
  have : (fun x => phaseInner x (c • u)) '' K = c • ((fun x => phaseInner x u) '' K) := by
    rw [← Set.image_smul, Set.image_image]
    simp [pI_smul_right]
  rw [this, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

lemma pI_self_eq_zero {x : Phase n} (h : phaseInner x x = 0) : x = 0 := by
  have h1 := norm_sq_le_pI x
  rw [h] at h1
  have h2 : ‖x‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

lemma ext_pI {x y : Phase n} (h : ∀ w, phaseInner x w = phaseInner y w) : x = y := by
  have h1 := h (x - y)
  have : phaseInner (x - y) (x - y) = 0 := by rw [pI_sub_left, h1, sub_self]
  exact sub_eq_zero.1 (pI_self_eq_zero this)

lemma part_mem {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t) (i : Fin (N + 1)) :
    0 ≤ t i ∧ t i ≤ 1 := by
  constructor
  · rw [← ht.1]; exact ht.2.2.monotone (Fin.zero_le _)
  · rw [← ht.2.1]; exact ht.2.2.monotone (Fin.le_last _)

lemma part_le {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t) (i : Fin N) :
    t i.castSucc ≤ t i.succ :=
  ht.2.2.monotone (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le

/-- The uniform partition `i / N`. -/
lemma unif_part {N : ℕ} (hN : 0 < N) :
    IsPart (fun i : Fin (N + 1) => (i : ℝ) / N) ∧
      MeshLE (fun i : Fin (N + 1) => (i : ℝ) / N) (1 / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨⟨by simp, by simp [hN'.ne'], fun i j hij => ?_⟩, fun i => ?_⟩
  · simp only
    apply div_lt_div_of_pos_right _ hN'
    exact_mod_cast hij
  · simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    rw [← sub_div]; simp

/-- The integrals over the cells of a partition add up. -/
lemma sum_cells {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : ∀ a b, IntervalIntegrable f volume a b) :
    ∀ (N : ℕ) (t : Fin (N + 1) → ℝ),
      ∑ i : Fin N, ∫ x in t i.castSucc..t i.succ, f x = ∫ x in t 0..t (Fin.last N), f x
  | 0, t => by simp
  | N + 1, t => by
    rw [Fin.sum_univ_castSucc]
    have ih := sum_cells hf N (fun i => t i.castSucc)
    simp only [Fin.succ_castSucc] at ih ⊢
    rw [ih, Fin.castSucc_zero, Fin.succ_last,
      intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _)]

/-! ### Lipschitz curves -/
lemma lip_ftc {z : ℝ → Phase n} {M : ℝ≥0} (hL : LipschitzWith M z) :
    LocallyIntegrable (deriv z) volume ∧ ∀ a b, z b - z a = ∫ s in a..b, deriv z s := by
  have hb : ∀ t, ‖deriv z t‖ ≤ M := fun t => norm_deriv_le_of_lipschitz hL
  have hli : LocallyIntegrable (deriv z) volume := by
    refine (continuous_const (y := (M : ℝ))).locallyIntegrable.mono
      (measurable_deriv z).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    simpa using hb t
  refine ⟨hli, fun a b => ?_⟩
  refine ext_pI fun w => ?_
  have hfL : LipschitzWith (‖pIL w‖₊ * M) (fun t => phaseInner (z t) w) := by
    have := (pIL w).lipschitz.comp hL
    simpa [Function.comp_def, pIL_apply] using this
  have hftc :=
    (hfL.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hd : ∀ᵐ t, deriv (fun t => phaseInner (z t) w) t = pIL w (deriv z t) := by
    filter_upwards [hL.ae_differentiableAt_real] with t ht
    have := ((pIL w).hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).deriv
    simpa [Function.comp_def, pIL_apply] using this
  rw [intervalIntegral.integral_congr_ae (hd.mono fun t ht _ => ht),
    (pIL w).intervalIntegral_comp_comm (ii_of_li hli a b)] at hftc
  rw [pI_sub_left, ← pIL_apply w (∫ s in a..b, deriv z s), hftc]

lemma isAC_of_lipschitz {z : ℝ → Phase n} {M : ℝ≥0} (hL : LipschitzWith M z) :
    IsAC z ∧ ∀ t, ‖deriv z t‖ ≤ M :=
  ⟨⟨deriv z, (lip_ftc hL).1, (lip_ftc hL).2⟩, fun _ => norm_deriv_le_of_lipschitz hL⟩

lemma supp_negJ_le_integral {K : Set (Phase n)} (hK : IsConvexDomain K) {v : ℝ → Phase n}
    (hv : LocallyIntegrable v volume) {a b : ℝ} (hab : a ≤ b) :
    supp K (-J (∫ s in a..b, v s)) ≤ ∫ s in a..b, supp K (-J (v s)) := by
  obtain ⟨k0, hk0⟩ := hK.2.2.mono interior_subset
  refine csSup_le (Set.Nonempty.image _ ⟨k0, hk0⟩) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only
  rw [pI_negJ, ← integral_pI_const hv]
  refine intervalIntegral.integral_mono_on hab (ii_pI (w := fun _ => J x) continuous_const hv a b)
    (ii_supp hK hv a b) fun s _ => ?_
  rw [← pI_negJ]
  exact le_csSup (bdd_supp hK.1 _) (mem_image_of_mem _ hx)

/-! ### Riemann sums of the action -/
lemma action_sub_rsum {z v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t) :
    action z - rsum z t = 1 / 2 * ∑ i : Fin N,
      ∫ s in t i.castSucc..t i.succ, phaseInner (J (z s - z (t i.castSucc))) (v s) := by
  have hzc := cont_of_ac hv hf
  have hii : ∀ a b, IntervalIntegrable (fun s => phaseInner (J (z s)) (v s)) volume a b :=
    ii_pI (w := fun s => J (z s)) (continuous_J.comp hzc) hv
  have hs := sum_cells hii N t
  rw [ht.1, ht.2.1] at hs
  rw [action_eq hv hf, ← hs]
  unfold rsum
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf, ← integral_pI_const hv,
    ← intervalIntegral.integral_sub (hii _ _) (ii_pI (w := fun _ => J (z (t i.castSucc)))
      continuous_const hv _ _)]
  congr 1; ext s; rw [J_sub, pI_sub_left]

lemma abs_action_sub_rsum_le_of {z v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t)
    {η : ℝ} (hη : ∀ i : Fin N, ∀ s ∈ Icc (t i.castSucc) (t i.succ), ‖z s - z (t i.castSucc)‖ ≤ η) :
    |action z - rsum z t| ≤ η * ∫ s in (0 : ℝ)..1, ‖v s‖ := by
  have hzc := cont_of_ac hv hf
  rw [action_sub_rsum hv hf ht]
  have hvn : ∀ a b, IntervalIntegrable (fun s => ‖v s‖) volume a b :=
    fun a b => (ii_of_li hv a b).norm
  have hs := sum_cells hvn N t
  rw [ht.1, ht.2.1] at hs
  rw [← hs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := part_le ht i
  refine (mul_le_mul_of_nonneg_left (intervalIntegral.abs_integral_le_integral_abs hle)
    (by norm_num)).trans ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hle ?_ ((hvn _ _).const_mul η) fun s hs => ?_
  · exact ((ii_pI (w := fun s => J (z s - z (t i.castSucc)))
      (continuous_J.comp (hzc.sub continuous_const)) hv _ _).abs).const_mul _
  · have h1 := abs_pI_le (J (z s - z (t i.castSucc))) (v s)
    rw [norm_J] at h1
    have h2 := hη i s hs
    have h3 := norm_nonneg (v s)
    nlinarith

lemma tendsto_rsum {z : ℝ → Phase n} (hz : IsLoop z) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (N : ℕ) (t : Fin (N + 1) → ℝ), IsPart t → MeshLE t δ →
      |action z - rsum z t| ≤ ε := by
  obtain ⟨-, v, hv, hf⟩ := hz
  have hzc := cont_of_ac hv hf
  set V := ∫ s in (0 : ℝ)..1, ‖v s‖
  have hV : 0 ≤ V := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  have hη : 0 < ε / (V + 1) := by positivity
  obtain ⟨δ, hδ, hzδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous hzc.continuousOn) _ hη
  refine ⟨δ / 2, by positivity, fun N t ht hm => ?_⟩
  refine (abs_action_sub_rsum_le_of hv hf ht (η := ε / (V + 1)) fun i s hs => ?_).trans ?_
  · have hi := part_mem ht i.castSucc
    have hj := part_mem ht i.succ
    have := hzδ s ⟨hi.1.trans hs.1, hs.2.trans hj.2⟩ (t i.castSucc) hi
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hm i, hs.1, hs.2])
    rw [dist_eq_norm] at this
    exact this.le
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith

lemma abs_action_sub_rsum_le {z : ℝ → Phase n} {M : ℝ≥0} (hz : Function.Periodic z 1)
    (hL : LipschitzWith M z) {δ : ℝ} {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t)
    (hδ : MeshLE t δ) : |action z - rsum z t| ≤ 2 * (M : ℝ) ^ 2 * δ := by
  obtain ⟨hli, hf⟩ := lip_ftc hL
  have hδ0 : 0 ≤ δ := by
    cases N with
    | zero =>
      exfalso
      have h1 := ht.2.1
      rw [show Fin.last 0 = 0 from rfl, ht.1] at h1
      exact zero_ne_one h1
    | succ N =>
      have h1 := hδ 0
      have h2 := ht.2.2 (show (0 : Fin (N + 1)).castSucc < (0 : Fin (N + 1)).succ from Fin.castSucc_lt_succ)
      linarith
  have hM : ∫ s in (0 : ℝ)..1, ‖deriv z s‖ ≤ M := by
    have := intervalIntegral.integral_mono_on zero_le_one (ii_of_li hli 0 1).norm
      (intervalIntegrable_const (c := (M : ℝ))) fun s _ => norm_deriv_le_of_lipschitz hL
    simpa using this
  refine (abs_action_sub_rsum_le_of hli hf ht (η := M * δ) fun i s hs => ?_).trans ?_
  · have := hL.dist_le_mul s (t i.castSucc)
    rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (by linarith [hs.1])] at this
    have h2 : s - t i.castSucc ≤ δ := by linarith [hs.2, hδ i]
    exact this.trans (mul_le_mul_of_nonneg_left h2 M.2)
  · have hM0 : (0 : ℝ) ≤ M := M.2
    have hint0 : 0 ≤ ∫ s in (0 : ℝ)..1, ‖deriv z s‖ :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
    nlinarith [mul_nonneg hM0 hδ0, mul_nonneg (mul_nonneg hM0 hM0) hδ0]

/-! ## Reparametrization by `h_L`-arclength -/
/-- With `B(0, r) ⊆ K`, `h_K(u) ≥ (r/2)‖u‖`. -/
lemma supp_lower0 {K : Set (Phase n)} (hK : IsConvexDomain K) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Phase n) r ⊆ K) (u : Phase n) :
    r / 2 * ‖u‖ ≤ supp K u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [supp_zero ⟨0, hball (Metric.mem_ball_self hr)⟩]; simp
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set s := r / (2 * ‖u‖) with hs
  have hs0 : 0 < s := by positivity
  have hsu : s * ‖u‖ = r / 2 := by rw [hs]; field_simp
  have hz : s • u ∈ K := hball (by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hsu]
    linarith)
  have h1 : phaseInner (s • u) u ≤ supp K u :=
    le_csSup (bdd_supp hK.1 u) (mem_image_of_mem _ hz)
  rw [pI_smul_left] at h1
  have h2 := norm_sq_le_pI u
  have : r / 2 * ‖u‖ = s * ‖u‖ ^ 2 := by rw [← hsu]; ring
  nlinarith [mul_le_mul_of_nonneg_left h2 hs0.le]

/-- An `h_K`-Lipschitz curve is Lipschitz. -/
lemma lip_of_hbound {K : Set (Phase n)} (hK : IsConvexDomain K) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Phase n) r ⊆ K) {w : ℝ → Phase n} {c : ℝ}
    (hw : ∀ a b, a ≤ b → supp K (-J (w b - w a)) ≤ c * (b - a)) :
    LipschitzWith (Real.toNNReal (2 / r * c)) w := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have key : ∀ x y : ℝ, y ≤ x → dist (w x) (w y) ≤ (Real.toNNReal (2 / r * c) : ℝ) * dist x y := by
    intro x y hxy
    rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hxy)]
    have h1 := supp_lower0 hK hr hball (-J (w x - w y))
    rw [norm_negJ] at h1
    have h2 := hw y x hxy
    have h3 : ‖w x - w y‖ ≤ 2 / r * c * (x - y) := by
      rw [show 2 / r * c * (x - y) = 2 / r * (c * (x - y)) by ring]
      have : ‖w x - w y‖ = 2 / r * (r / 2 * ‖w x - w y‖) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    exact h3.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (sub_nonneg.2 hxy))
  rcases le_total y x with h | h
  · exact key x y h
  · rw [dist_comm, dist_comm x y]; exact key y x h

lemma deriv_periodic {z : ℝ → Phase n} (hz : Function.Periodic z 1) :
    Function.Periodic (deriv z) 1 := fun t => by
  have h : (fun x => z (x + 1)) = z := funext hz
  rw [← deriv_comp_add_const, h]

/-- Reparametrization of a loop to constant `h_K`-speed (up to `ε`), keeping the action. -/
lemma exists_reparam_h {K : Set (Phase n)} (hK : IsConvexDomain K) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : Phase n) r ⊆ K) {z : ℝ → Phase n} (hz : IsLoop z) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ w : ℝ → Phase n, Function.Periodic w 1 ∧ action w = action z ∧
      ∀ a b, a ≤ b → supp K (-J (w b - w a)) ≤ (ell K z + ε) * (b - a) := by
  obtain ⟨v', hv', hf'⟩ := hz.2
  have hv : LocallyIntegrable (deriv z) volume :=
    hv'.congr (Filter.EventuallyEq.symm (deriv_ae hv' hf'))
  have hf : ∀ a b, z b - z a = ∫ s in a..b, deriv z s := fun a b => by
    rw [hf' a b]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [deriv_ae hv' hf'] with t ht _
    rw [ht]
  have hvp := deriv_periodic hz.1
  set g : ℝ → ℝ := fun t => supp K (-J (deriv z t)) + ε with hgdef
  have hgp : Function.Periodic g 1 := fun t => by simp only [hgdef, hvp t]
  have hgi : ∀ a b, IntervalIntegrable g volume a b := fun a b =>
    (ii_supp hK hv a b).add intervalIntegrable_const
  have hsnn : ∀ t, 0 ≤ supp K (-J (deriv z t)) := fun t => by
    have := supp_lower0 hK hr hball (-J (deriv z t))
    have : 0 ≤ r / 2 * ‖-J (deriv z t)‖ := by positivity
    linarith
  have hgε : ∀ t, ε ≤ g t := fun t => by simp only [hgdef]; linarith [hsnn t]
  set c := ell K z + ε with hcdef
  have hc : 0 < c := by linarith [ell_nonneg hK hz.1 hz.2]
  have hint01 : ∫ t in (0 : ℝ)..1, g t = c := by
    simp only [hgdef]
    rw [intervalIntegral.integral_add (ii_supp hK hv 0 1) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp [hcdef, ell, supp]
  have hper1 : ∀ t, ∫ s in t..t + 1, g s = c := fun t => by
    rw [hgp.intervalIntegral_add_eq t 0, zero_add, hint01]
  have hmono : ∀ a b, a ≤ b → ε * (b - a) ≤ ∫ s in a..b, g s := fun a b hab => by
    have := intervalIntegral.integral_mono_on hab intervalIntegrable_const (hgi a b)
      (fun t _ => hgε t)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  set F : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, g s) / c with hFdef
  have hFsub : ∀ a b, F b - F a = (∫ s in a..b, g s) / c := fun a b => by
    simp only [hFdef]
    rw [← sub_div, intervalIntegral.integral_interval_sub_left (hgi 0 b) (hgi 0 a)]
  have hFcont : Continuous F :=
    (intervalIntegral.continuous_primitive hgi 0).div_const c
  have hFlow : ∀ a b, a ≤ b → ε / c * (b - a) ≤ F b - F a := fun a b hab => by
    rw [hFsub, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
    exact hmono a b hab
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hFsm : StrictMono F := fun a b hab => by
    have := hFlow a b hab.le
    have : 0 < ε / c * (b - a) := by have := sub_pos.2 hab; positivity
    linarith
  have hεc : 0 < ε / c := by positivity
  have htop : Tendsto F atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hεc)
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := hFlow 0 t ht
    simp only [hF0, sub_zero, id] at this ⊢
    exact this
  have hbot : Tendsto F atBot atBot := by
    refine tendsto_atBot_mono' atBot ?_ (tendsto_id.const_mul_atBot hεc)
    filter_upwards [eventually_le_atBot 0] with t ht
    have := hFlow t 0 ht
    simp only [hF0, zero_sub, id] at this ⊢
    linarith
  set e := StrictMono.orderIsoOfSurjective F hFsm (hFcont.surjective htop hbot)
  have he : ∀ t, e t = F t := fun t => rfl
  have he0 : e 0 = 0 := by rw [he, hF0]
  have he1 : e 1 = 1 := by
    rw [he]; simp only [hFdef]; rw [hint01, div_self hc.ne']
  have hper : ∀ t, e (t + 1) = e t + 1 := by
    intro t
    rw [he, he, ← sub_eq_iff_eq_add', hFsub, hper1, div_self hc.ne']
  have hH : ∀ a b, a ≤ b → supp K (-J (z b - z a)) ≤ c * (e b - e a) := by
    intro a b hab
    rw [he, he, hFsub, hf a b]
    calc supp K (-J (∫ s in a..b, deriv z s)) ≤ ∫ s in a..b, supp K (-J (deriv z s)) :=
          supp_negJ_le_integral hK hv hab
      _ ≤ ∫ s in a..b, g s :=
          intervalIntegral.integral_mono_on hab (ii_supp hK hv a b) (hgi a b)
            (fun t _ => by simp only [hgdef]; linarith)
      _ = c * ((∫ s in a..b, g s) / c) := by field_simp
  have hμ : ∀ a b, a ≤ b → b - a ≤ c / ε * (e b - e a) := by
    intro a b hab
    rw [he, he]
    have := hFlow a b hab
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    linarith
  -- the reparametrized loop
  set ψ := e.symm with hψdef
  have hψ0 : ψ 0 = 0 := by rw [hψdef, OrderIso.symm_apply_eq, he0]
  have hψ1 : ψ 1 = 1 := by rw [hψdef, OrderIso.symm_apply_eq, he1]
  have hψper : ∀ s, ψ (s + 1) = ψ s + 1 := fun s => by
    rw [hψdef, OrderIso.symm_apply_eq, hper, OrderIso.apply_symm_apply]
  have heψ : ∀ s, e (ψ s) = s := fun s => e.apply_symm_apply s
  set w : ℝ → Phase n := fun s => z (ψ s) with hwdef
  have hwp : Function.Periodic w 1 := fun s => by
    simp only [hwdef, hψper]; exact hz.1 _
  have hwH : ∀ a b, a ≤ b → supp K (-J (w b - w a)) ≤ c * (b - a) := by
    intro a b hab
    have := hH (ψ a) (ψ b) (ψ.monotone hab)
    rwa [heψ, heψ] at this
  have hwL := lip_of_hbound hK hr hball hwH
  have hwloop : IsLoop w := ⟨hwp, (isAC_of_lipschitz hwL).1⟩
  have hpartψ : ∀ {N : ℕ} {t : Fin (N + 1) → ℝ}, IsPart t → IsPart (ψ ∘ t) := by
    intro N t ht
    exact ⟨by simp [ht.1, hψ0], by simp [ht.2.1, hψ1], ψ.strictMono.comp ht.2.2⟩
  refine ⟨w, hwp, ?_, hwH⟩
  refine eq_of_forall_dist_le fun δ hδ => ?_
  obtain ⟨δw, hδw, hw⟩ := tendsto_rsum hwloop (half_pos hδ)
  obtain ⟨δz, hδz, hzr⟩ := tendsto_rsum hz (half_pos hδ)
  set μ := c / ε
  have hμ0 : 0 ≤ μ := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / δw) ((μ + 1) / δz))
  have hNpos : (0 : ℝ) < N :=
    lt_of_le_of_lt (le_max_of_le_left (by positivity)) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  obtain ⟨hpt, hmesh⟩ := unif_part hN0
  set t : Fin (N + 1) → ℝ := fun i => (i : ℝ) / N
  have hmw : MeshLE t δw := fun i => by
    refine (hmesh i).trans ?_
    rw [div_le_iff₀ hNpos]
    have := (le_max_left _ _).trans hN.le
    rw [div_le_iff₀ hδw] at this
    linarith
  have hmz : MeshLE (ψ ∘ t) δz := fun i => by
    have h1 := hμ _ _ (ψ.monotone (hpt.2.2.monotone (Fin.castSucc_le_succ i)))
    simp only [Function.comp, heψ] at h1 ⊢
    have h2 := hmesh i
    have h3 : μ * (t i.succ - t i.castSucc) ≤ μ * (1 / N) := mul_le_mul_of_nonneg_left h2 hμ0
    have h4 : μ * (1 / N) ≤ δz := by
      have := (le_max_right _ _).trans hN.le
      rw [div_le_iff₀ hδz] at this
      rw [mul_one_div, div_le_iff₀ hNpos]
      nlinarith
    linarith
  have e1 := hw N t hpt hmw
  have e2 := hzr N (ψ ∘ t) (hpartψ hpt) hmz
  have : rsum w t = rsum z (ψ ∘ t) := rfl
  rw [Real.dist_eq]
  rw [this] at e1
  calc |action w - action z| = |(action w - rsum z (ψ ∘ t)) - (action z - rsum z (ψ ∘ t))| := by
        ring_nf
    _ ≤ |action w - rsum z (ψ ∘ t)| + |action z - rsum z (ψ ∘ t)| := abs_sub _ _
    _ ≤ δ := by linarith

/-! ## The kernel `cos(π s)^{2M}` on `[-1/2, 1/2]` -/
/-- The kernel. -/
def ker (M : ℕ) (s : ℝ) : ℝ := Real.cos (Real.pi * s) ^ (2 * M)

/-- Its mass. -/
def kI (M : ℕ) : ℝ := ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s

lemma continuous_ker (M : ℕ) : Continuous (ker M) := by unfold ker; fun_prop

lemma ker_nonneg (M : ℕ) (s : ℝ) : 0 ≤ ker M s := by
  unfold ker; rw [pow_mul]; positivity

lemma ker_periodic (M : ℕ) : Function.Periodic (ker M) 1 := fun s => by
  unfold ker
  rw [mul_add, mul_one, Real.cos_add_pi, pow_mul, pow_mul, neg_sq]

lemma kI_pos (M : ℕ) : 0 < kI M := by
  unfold kI
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_ker M).intervalIntegrable _ _) (fun x hx => ?_) (by norm_num)
  unfold ker
  have : 0 < Real.cos (Real.pi * x) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]
  positivity

lemma integral_cos_pi_pow (k : ℕ) :
    ∫ s in (-(1 / 2) : ℝ)..(1 / 2), Real.cos (Real.pi * s) ^ k =
      Real.pi⁻¹ * ∫ x in (-(Real.pi / 2))..(Real.pi / 2), Real.cos x ^ k := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ k) Real.pi_pos.ne',
    smul_eq_mul]
  congr 3 <;> ring

lemma kI_succ (M : ℕ) :
    ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s * Real.cos (Real.pi * s) ^ 2 =
      (2 * M + 1) / (2 * M + 2) * kI M := by
  have e : ∀ s, ker M s * Real.cos (Real.pi * s) ^ 2 = Real.cos (Real.pi * s) ^ (2 * M + 2) :=
    fun s => by unfold ker; ring
  simp only [e]
  simp only [kI, ker, integral_cos_pi_pow]
  rw [integral_cos_pow]
  simp only [Real.cos_neg, Real.cos_pi_div_two]
  push_cast
  simp
  ring

/-- `4 s² ≤ 1 - cos(π s)²` on `[-1/2, 1/2]` (Jordan). -/
lemma four_sq_le (s : ℝ) (hs : |s| ≤ 1 / 2) : 4 * s ^ 2 ≤ 1 - Real.cos (Real.pi * s) ^ 2 := by
  rw [← Real.sin_sq]
  have h0 : 0 ≤ Real.pi * |s| := by positivity
  have h1 : Real.pi * |s| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have h2 := Real.mul_le_sin h0 h1
  rw [show 2 / Real.pi * (Real.pi * |s|) = 2 * |s| by field_simp] at h2
  have h3 : Real.sin (Real.pi * |s|) ^ 2 = Real.sin (Real.pi * s) ^ 2 := by
    rcases abs_cases s with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · rw [h, mul_neg, Real.sin_neg, neg_sq]
  rw [← h3, show 4 * s ^ 2 = (2 * |s|) ^ 2 by rw [mul_pow, sq_abs]; ring]
  exact pow_le_pow_left₀ (by positivity) h2 2

/-- The first moment of the normalized kernel is small. -/
lemma ker_moment (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s * |s| ≤ (ε + 1 / (8 * ε * (M + 1))) * kI M := by
  have hle : ∀ s ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ker M s * |s| ≤
      ε * ker M s + (4 * ε)⁻¹ * (ker M s - ker M s * Real.cos (Real.pi * s) ^ 2) := by
    intro s hs
    have hs' : |s| ≤ 1 / 2 := abs_le.2 ⟨hs.1, hs.2⟩
    have h4 := four_sq_le s hs'
    have hk := ker_nonneg M s
    have h5 : |s| ≤ ε + s ^ 2 / ε := by
      have : 0 ≤ (|s| - ε) ^ 2 := sq_nonneg _
      have e : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
      rw [e]
      rw [show ε + |s| ^ 2 / ε = (ε ^ 2 + |s| ^ 2) / ε by field_simp, le_div_iff₀ hε]
      nlinarith
    have h6 : s ^ 2 / ε ≤ (4 * ε)⁻¹ * (1 - Real.cos (Real.pi * s) ^ 2) := by
      rw [div_eq_mul_inv, mul_comm, mul_inv]
      have : (0 : ℝ) ≤ ε⁻¹ := by positivity
      nlinarith
    calc ker M s * |s| ≤ ker M s * (ε + (4 * ε)⁻¹ * (1 - Real.cos (Real.pi * s) ^ 2)) :=
          mul_le_mul_of_nonneg_left (h5.trans (by linarith)) hk
      _ = _ := by ring
  have hc : Continuous fun s => ker M s * Real.cos (Real.pi * s) ^ 2 :=
    (continuous_ker M).mul (by fun_prop)
  have hg : IntervalIntegrable (fun s => ε * ker M s + (4 * ε)⁻¹ *
      (ker M s - ker M s * Real.cos (Real.pi * s) ^ 2)) volume (-(1 / 2)) (1 / 2) :=
    (((continuous_ker M).const_mul ε).add
      (((continuous_ker M).sub hc).const_mul _)).intervalIntegrable _ _
  refine (intervalIntegral.integral_mono_on (by norm_num)
    (((continuous_ker M).mul continuous_abs).intervalIntegrable _ _) hg hle).trans (le_of_eq ?_)
  have h1 : IntervalIntegrable (fun s => ε * ker M s) volume (-(1 / 2)) (1 / 2) :=
    ((continuous_ker M).const_mul ε).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s => (4 * ε)⁻¹ *
      (ker M s - ker M s * Real.cos (Real.pi * s) ^ 2)) volume (-(1 / 2)) (1 / 2) :=
    (((continuous_ker M).sub hc).const_mul _).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun s => ker M s) volume (-(1 / 2)) (1 / 2) :=
    (continuous_ker M).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun s => ker M s * Real.cos (Real.pi * s) ^ 2) volume
      (-(1 / 2)) (1 / 2) := hc.intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub h3 h4, kI_succ]
  rw [← kI]
  have hM : (0 : ℝ) < M + 1 := by positivity
  field_simp
  ring

/-! ## Smoothing -/
/-- The smoothed loop `t ↦ (1/I) ∫_{-1/2}^{1/2} ker(s) w(t - s) ds`. -/
def smooth (w : ℝ → Phase n) (M : ℕ) (t : ℝ) : Phase n :=
  (kI M)⁻¹ • ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s • w (t - s)

lemma ii_ker_smul {w : ℝ → Phase n} (hw : Continuous w) (M : ℕ) (t : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun s => ker M s • w (t - s)) volume a b :=
  ((continuous_ker M).smul (hw.comp (continuous_const.sub continuous_id))).intervalIntegrable _ _

lemma smooth_sub {w : ℝ → Phase n} (hw : Continuous w) (M : ℕ) (a b : ℝ) :
    smooth w M b - smooth w M a =
      (kI M)⁻¹ • ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s • (w (b - s) - w (a - s)) := by
  unfold smooth
  rw [← smul_sub, ← intervalIntegral.integral_sub (ii_ker_smul hw M b _ _)
    (ii_ker_smul hw M a _ _)]
  simp only [smul_sub]

lemma smooth_hbound {K : Set (Phase n)} (hK : IsConvexDomain K) {w : ℝ → Phase n}
    (hw : Continuous w) {c : ℝ}
    (hH : ∀ a b, a ≤ b → supp K (-J (w b - w a)) ≤ c * (b - a)) (M : ℕ) :
    ∀ a b, a ≤ b → supp K (-J (smooth w M b - smooth w M a)) ≤ c * (b - a) := by
  intro a b hab
  have hI := kI_pos M
  rw [smooth_sub hw M a b, J_smul, ← smul_neg, supp_smul K (inv_nonneg.2 hI.le)]
  set v : ℝ → Phase n := fun s => ker M s • (w (b - s) - w (a - s)) with hvdef
  have hvc : Continuous v := (continuous_ker M).smul
    ((hw.comp (continuous_const.sub continuous_id)).sub
      (hw.comp (continuous_const.sub continuous_id)))
  have hv : LocallyIntegrable v volume := hvc.locallyIntegrable
  have h1 := supp_negJ_le_integral hK hv (show (-(1 / 2) : ℝ) ≤ 1 / 2 by norm_num)
  have h2 : ∫ s in (-(1 / 2) : ℝ)..(1 / 2), supp K (-J (v s)) ≤
      ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s * (c * (b - a)) := by
    refine intervalIntegral.integral_mono_on (by norm_num) (ii_supp hK hv _ _)
      (((continuous_ker M).mul continuous_const).intervalIntegrable _ _) (fun s _ => ?_)
    simp only [hvdef]
    rw [J_smul, ← smul_neg, supp_smul K (ker_nonneg M s)]
    have := hH (a - s) (b - s) (by linarith)
    rw [show b - s - (a - s) = b - a by ring] at this
    exact mul_le_mul_of_nonneg_left this (ker_nonneg M s)
  rw [intervalIntegral.integral_mul_const, ← kI] at h2
  have h3 := h1.trans h2
  calc (kI M)⁻¹ * supp K (-J (∫ s in (-(1 / 2) : ℝ)..(1 / 2), v s))
      ≤ (kI M)⁻¹ * (kI M * (c * (b - a))) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = c * (b - a) := by field_simp

lemma smooth_err {w : ℝ → Phase n} (hw : Continuous w) {Λ : ℝ}
    (hL : ∀ x y, ‖w x - w y‖ ≤ Λ * |x - y|) (M : ℕ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖smooth w M t - w t‖ ≤ Λ * (ε + 1 / (8 * ε * (M + 1))) := by
  have hI := kI_pos M
  have hΛ : 0 ≤ Λ := by
    have := hL 1 0
    have h0 : (0 : ℝ) ≤ ‖w 1 - w 0‖ := norm_nonneg _
    norm_num at this
    linarith
  have e1 : w t = (kI M)⁻¹ • ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s • w t := by
    rw [intervalIntegral.integral_smul_const, ← kI, smul_smul, inv_mul_cancel₀ hI.ne', one_smul]
  have e2 : smooth w M t - w t =
      (kI M)⁻¹ • ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s • (w (t - s) - w t) := by
    conv_lhs => rw [e1]
    unfold smooth
    have hc : IntervalIntegrable (fun s => ker M s • w t) volume (-(1 / 2)) (1 / 2) :=
      ((continuous_ker M).smul continuous_const).intervalIntegrable _ _
    rw [← smul_sub, ← intervalIntegral.integral_sub (ii_ker_smul hw M t _ _) hc]
    simp only [smul_sub]
  rw [e2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hI)]
  have h1 := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := fun s => ker M s • (w (t - s) - w t)) (show (-(1 / 2) : ℝ) ≤ 1 / 2 by norm_num)
  have h2 : ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ‖ker M s • (w (t - s) - w t)‖ ≤
      ∫ s in (-(1 / 2) : ℝ)..(1 / 2), Λ * (ker M s * |s|) := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_
      ((((continuous_ker M).mul continuous_abs).const_mul Λ).intervalIntegrable _ _)
      (fun s _ => ?_)
    · exact (((continuous_ker M).smul ((hw.comp (continuous_const.sub continuous_id)).sub
        continuous_const)).norm).intervalIntegrable _ _
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ker_nonneg M s)]
      have := hL (t - s) t
      rw [show t - s - t = -s by ring, abs_neg] at this
      have := mul_le_mul_of_nonneg_left this (ker_nonneg M s)
      linarith
  rw [intervalIntegral.integral_const_mul] at h2
  have h3 := ker_moment M hε
  calc (kI M)⁻¹ * ‖∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s • (w (t - s) - w t)‖
      ≤ (kI M)⁻¹ * (Λ * ((ε + 1 / (8 * ε * (M + 1))) * kI M)) := by
        refine mul_le_mul_of_nonneg_left ((h1.trans h2).trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h3 hΛ
    _ = Λ * (ε + 1 / (8 * ε * (M + 1))) := by field_simp

lemma smooth_periodic {w : ℝ → Phase n} (hw : Function.Periodic w 1) (M : ℕ) :
    Function.Periodic (smooth w M) 1 := fun t => by
  unfold smooth
  congr 2
  funext s
  rw [show t + 1 - s = t - s + 1 by ring, hw]

/-! ## The smoothed loop is a trigonometric polynomial -/
/-- The kernel coefficients. -/
def kc (M : ℕ) (m : ℤ) : ℂ := (Nat.choose (2 * M) (m + M).toNat : ℂ) / 4 ^ M

lemma sum_Icc_reindex {E : Type*} [AddCommMonoid E] (M : ℕ) (g : ℤ → E) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M, g m = ∑ j ∈ Finset.range (2 * M + 1), g ((j : ℤ) - M) := by
  refine Finset.sum_nbij' (fun m => (m + M).toNat) (fun j => (j : ℤ) - M) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    have := Finset.mem_Icc.1 hm
    exact Finset.mem_range.2 (by omega)
  · intro j hj
    have := Finset.mem_range.1 hj
    exact Finset.mem_Icc.2 (by omega)
  · intro m hm
    have := Finset.mem_Icc.1 hm
    omega
  · intro j _
    omega
  · intro m hm
    have := Finset.mem_Icc.1 hm
    congr 1
    omega

lemma exp_eq_zpow (m : ℤ) (y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * m * y) =
      Complex.exp (2 * Real.pi * Complex.I * y) ^ m := by
  rw [← Complex.exp_int_mul]; congr 1; ring

lemma ker_trig (M : ℕ) (y : ℝ) :
    ((ker M y : ℝ) : ℂ) = ∑ m ∈ Finset.Icc (-(M : ℤ)) M,
      kc M m * Complex.exp (2 * Real.pi * Complex.I * m * y) := by
  set X := Complex.exp (2 * Real.pi * Complex.I * y) with hX
  have hX0 : X ≠ 0 := Complex.exp_ne_zero _
  have h2 : Complex.cos (2 * Real.pi * y) = (X + X⁻¹) / 2 := by
    rw [hX, ← Complex.exp_neg, eq_div_iff two_ne_zero, mul_comm, Complex.two_cos]
    congr 1 <;> congr 1 <;> ring
  have hc : ((Real.cos (Real.pi * y) ^ 2 : ℝ) : ℂ) = X⁻¹ * (X + 1) ^ 2 / 4 := by
    rw [Real.cos_sq]
    push_cast
    rw [show (2 : ℂ) * (Real.pi * y) = 2 * Real.pi * y by ring, h2]
    field_simp
    ring
  have hk : ((ker M y : ℝ) : ℂ) = (X ^ M)⁻¹ * (X + 1) ^ (2 * M) / 4 ^ M := by
    unfold ker
    rw [pow_mul, Complex.ofReal_pow, hc, div_pow, mul_pow, inv_pow, ← pow_mul]
  rw [hk, add_pow, Finset.mul_sum, Finset.sum_div, sum_Icc_reindex]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [exp_eq_zpow, ← hX, kc, show ((j : ℤ) - M + M).toNat = j by omega, one_pow, mul_one,
    zpow_sub₀ hX0, zpow_natCast, zpow_natCast]
  field_simp

/-- Convolution against a trigonometric kernel. -/
lemma conv_trig {f : ℝ → Vector (Fin n)} (hf : Continuous f) (D : ℕ) (κ : ℤ → ℂ) (t : ℝ) :
    ∫ u in (0 : ℝ)..1, (∑ m ∈ Finset.Icc (-(D : ℤ)) D,
        κ m * Complex.exp (2 * Real.pi * Complex.I * m * (t - u))) • f u =
      trigLoop D (fun m => κ m •
        ∫ u in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I * m * u)) • f u) t := by
  unfold trigLoop
  simp only [Finset.sum_smul]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul]
    congr 1
    funext u
    rw [smul_smul, smul_smul]
    congr 1
    rw [mul_comm (Complex.exp (2 * ↑Real.pi * Complex.I * ↑m * ↑t)) (κ m), mul_assoc (κ m),
      ← Complex.exp_add]
    congr 2
    ring
  · intro m _
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop

lemma rsmul_eq (r : ℝ) (v : Vector (Fin n)) : r • v = (r : ℂ) • v := by
  ext j; simp [Complex.real_smul]

/-- The `ℂⁿ` coefficients of the smoothed loop. -/
def smCoeff (w : ℝ → Phase n) (M : ℕ) (m : ℤ) : Vector (Fin n) :=
  (((kI M)⁻¹ : ℝ) * kc M m : ℂ) •
    ∫ u in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I * m * u)) • Capacities.Φ n (w u)

lemma smooth_trig {w : ℝ → Phase n} (hw : Continuous w) (hp : Function.Periodic w 1) (M : ℕ)
    (t : ℝ) : Capacities.Φ n (smooth w M t) = trigLoop M (smCoeff w M) t := by
  have hΦw : Continuous fun u => Capacities.Φ n (w u) := (Capacities.Φ n).continuous.comp hw
  unfold smooth
  rw [map_smul, ← (Capacities.Φ n).intervalIntegral_comp_comm (ii_ker_smul hw M t _ _)]
  simp only [map_smul]
  set G : ℝ → Vector (Fin n) := fun u => ker M (t - u) • Capacities.Φ n (w u) with hG
  have e1 : ∫ s in (-(1 / 2) : ℝ)..(1 / 2), ker M s • Capacities.Φ n (w (t - s)) =
      ∫ s in (-(1 / 2) : ℝ)..(1 / 2), G (t - s) := by
    simp only [hG, sub_sub_cancel]
  have hGp : Function.Periodic G 1 := fun u => by
    simp only [hG]
    rw [show t - (u + 1) = t - u - 1 by ring, (ker_periodic M).sub_eq, hp]
  rw [e1, intervalIntegral.integral_comp_sub_left G t,
    show t - -(1 / 2 : ℝ) = t - 1 / 2 + 1 by ring, hGp.intervalIntegral_add_eq (t - 1 / 2) 0,
    zero_add]
  unfold smCoeff
  rw [← conv_trig hΦw M (fun m => (((kI M)⁻¹ : ℝ) : ℂ) * kc M m) t,
    ← intervalIntegral.integral_smul]
  congr 1
  funext u
  simp only [hG]
  rw [smul_smul, rsmul_eq]
  congr 1
  push_cast
  rw [ker_trig, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

/-! ## Calculus and action of trigonometric loops -/
lemma hasDerivAt_trigLoop (D : ℕ) (b : ℤ → Vector (Fin n)) (t : ℝ) :
    HasDerivAt (trigLoop D b) (trigVel D b t) t := by
  unfold trigLoop trigVel
  refine HasDerivAt.fun_sum fun m _ => ?_
  refine HasDerivAt.smul_const ?_ (b m)
  have h : HasDerivAt (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I * m * z))
      (Complex.exp (2 * Real.pi * Complex.I * m * t) * (2 * Real.pi * Complex.I * m * 1)) t :=
    ((hasDerivAt_id (t : ℂ)).const_mul (2 * Real.pi * Complex.I * m)).cexp
  exact h.comp_ofReal.congr_deriv (by ring)

lemma continuous_trigVel (D : ℕ) (b : ℤ → Vector (Fin n)) : Continuous (trigVel D b) := by
  unfold trigVel; fun_prop

lemma integral_exp_int (k : ℤ) :
    ∫ t in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * k * t) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * Real.pi * Complex.I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      simp [hpi, Complex.I_ne_zero, this]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * k * ((1 : ℝ) : ℂ)) = 1 :=
      Complex.exp_eq_one_iff.2 ⟨k, by push_cast; ring⟩
    rw [h1]
    simp

lemma integral_conj_exp_mul (m l : ℤ) :
    ∫ t in (0 : ℝ)..1, (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * m * t)) *
      Complex.exp (2 * Real.pi * Complex.I * l * t) = if m = l then 1 else 0 := by
  have e : ∀ t : ℝ, (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * m * t)) *
      Complex.exp (2 * Real.pi * Complex.I * l * t) =
      Complex.exp (2 * Real.pi * Complex.I * ((l - m : ℤ) : ℂ) * t) := fun t => by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
    push_cast
    ring
  simp only [e]
  rw [integral_exp_int]
  by_cases h : m = l
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

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

lemma supportFn_Φ (L : Set (Phase n)) (y : Phase n) :
    supportFn (Capacities.Φ n '' L) (Capacities.Φ n y) = supp L y := by
  unfold supportFn supp
  rw [Set.image_image]
  simp only [inner_Φ]

lemma J_Ψ (v : Vector (Fin n)) : J (Capacities.Ψ n v) = Capacities.Ψ n (Complex.I • v) := by
  rw [← Capacities.Ψ_Φ (J (Capacities.Ψ n v)), Φ_J, Capacities.Φ_Ψ]

lemma integral_re' {F : ℝ → ℂ} (hF : IntervalIntegrable F volume 0 1) :
    ∫ t in (0 : ℝ)..1, (F t).re = (∫ t in (0 : ℝ)..1, F t).re :=
  Complex.reCLM.intervalIntegral_comp_comm hF

/-- The summand of `⟨i w, ẇ⟩`. -/
def tm (b : ℤ → Vector (Fin n)) (m l : ℤ) (t : ℝ) : ℂ :=
  (-Complex.I * (2 * Real.pi * Complex.I * l) * inner ℂ (b m) (b l)) *
    ((starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * m * t)) *
      Complex.exp (2 * Real.pi * Complex.I * l * t))

lemma continuous_tm (b : ℤ → Vector (Fin n)) (m l : ℤ) : Continuous (tm b m l) := by
  unfold tm; fun_prop

lemma trigAction_eq (D : ℕ) (b : ℤ → Vector (Fin n)) :
    action (fun t => Capacities.Ψ n (trigLoop D b t)) = trigAction D b := by
  have hd : ∀ t, deriv (fun t => Capacities.Ψ n (trigLoop D b t)) t =
      Capacities.Ψ n (trigVel D b t) := fun t =>
    ((Capacities.Ψ n).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_trigLoop D b t)).deriv
  unfold action
  simp only [hd]
  have hpt : ∀ t, phaseInner (J (Capacities.Ψ n (trigLoop D b t))) (Capacities.Ψ n (trigVel D b t)) =
      Complex.re (∑ m ∈ Finset.Icc (-(D : ℤ)) D, ∑ l ∈ Finset.Icc (-(D : ℤ)) D, tm b m l t) :=
    fun t => by
    rw [J_Ψ, ← inner_Φ, Capacities.Φ_Ψ, Capacities.Φ_Ψ]
    rw [OAI.FourierPolynomial.real_inner_eq_complex_re, RCLike.re_to_complex]
    congr 1
    unfold trigLoop trigVel tm
    rw [inner_smul_left, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_left, inner_smul_right, Complex.conj_I]
    ring
  simp only [hpt]
  have hS : IntervalIntegrable
      (fun t => ∑ m ∈ Finset.Icc (-(D : ℤ)) D, ∑ l ∈ Finset.Icc (-(D : ℤ)) D, tm b m l t)
      volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun l _ => continuous_tm b m l
  have hint : ∀ m l : ℤ, IntervalIntegrable (tm b m l) volume 0 1 := fun m l =>
    (continuous_tm b m l).intervalIntegrable _ _
  have hint2 : ∀ m : ℤ, IntervalIntegrable
      (fun t => ∑ l ∈ Finset.Icc (-(D : ℤ)) D, tm b m l t) volume 0 1 := fun m =>
    (continuous_finsetSum _ fun l _ => continuous_tm b m l).intervalIntegrable _ _
  rw [integral_re' hS, intervalIntegral.integral_finsetSum fun m _ => hint2 m]
  simp_rw [intervalIntegral.integral_finsetSum fun l _ => hint _ l]
  unfold tm
  simp_rw [intervalIntegral.integral_const_mul, integral_conj_exp_mul]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_Icc]
  unfold trigAction
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [if_pos (Finset.mem_Icc.1 hm)]
  have : -Complex.I * (2 * Real.pi * Complex.I * m) * inner ℂ (b m) (b m) =
      ((2 * Real.pi * m * ‖b m‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this, Complex.ofReal_re]
  ring

/-! ## Convergence of the action -/
lemma continuous_supp {K : Set (Phase n)} (hK : IsConvexDomain K) : Continuous (supp K) := by
  obtain ⟨R, hR⟩ := hK.1.exists_norm_le
  obtain ⟨k0, hk0⟩ := hK.2.2.mono interior_subset
  have hR0 : 0 ≤ R := (norm_nonneg k0).trans (hR k0 hk0)
  have hlip : LipschitzWith (Real.toNNReal (2 * R)) (supp K) := by
    refine LipschitzWith.of_le_add_mul _ fun x y => ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    exact supp_le_add hK.1 ⟨k0, hk0⟩ hR x y
  exact hlip.continuous

lemma cont_eval (x : ℝ) : Continuous fun w : ℝ → Phase n => w x := continuous_apply x

lemma continuous_rsum {N : ℕ} (t : Fin (N + 1) → ℝ) :
    Continuous fun w : ℝ → Phase n => rsum w t := by
  unfold rsum
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_pI.comp ((continuous_J.comp (cont_eval _)).prodMk
    ((cont_eval _).sub (cont_eval _)))

lemma tendsto_rsum_of_pointwise {zs : ℕ → ℝ → Phase n} {z : ℝ → Phase n}
    (h : ∀ x, Tendsto (fun M => zs M x) atTop (𝓝 (z x))) {N : ℕ} (t : Fin (N + 1) → ℝ) :
    Tendsto (fun M => rsum (zs M) t) atTop (𝓝 (rsum z t)) :=
  ((continuous_rsum t).tendsto z).comp (tendsto_pi_nhds.2 h)

lemma tendsto_action {zs : ℕ → ℝ → Phase n} {z : ℝ → Phase n} {Λ : ℝ≥0}
    (hzs : ∀ M, Function.Periodic (zs M) 1) (hzsL : ∀ M, LipschitzWith Λ (zs M))
    (hz : Function.Periodic z 1) (hzL : LipschitzWith Λ z)
    (h : ∀ x, Tendsto (fun M => zs M x) atTop (𝓝 (z x))) :
    Tendsto (fun M => action (zs M)) atTop (𝓝 (action z)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (6 * (Λ : ℝ) ^ 2 / η)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  obtain ⟨hpt, hmesh⟩ := unif_part hN0
  set t : Fin (N + 1) → ℝ := fun i => (i : ℝ) / N
  have hsmall : 2 * (Λ : ℝ) ^ 2 * (1 / N) < η / 3 := by
    rw [div_lt_iff₀ hη] at hN
    rw [mul_one_div, div_lt_iff₀ hNpos]
    linarith
  obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.1 (tendsto_rsum_of_pointwise h t) (η / 3) (by positivity)
  refine ⟨M₀, fun M hM => ?_⟩
  have e1 := abs_action_sub_rsum_le (hzs M) (hzsL M) hpt hmesh
  have e2 := abs_action_sub_rsum_le hz hzL hpt hmesh
  have e3 := hM₀ M hM
  rw [Real.dist_eq] at e3 ⊢
  calc |action (zs M) - action z|
      = |(action (zs M) - rsum (zs M) t) + (rsum (zs M) t - rsum z t) - (action z - rsum z t)| := by
        ring_nf
    _ ≤ |action (zs M) - rsum (zs M) t| + |rsum (zs M) t - rsum z t| + |action z - rsum z t| :=
        (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ < η := by linarith

lemma tendsto_smooth {w : ℝ → Phase n} (hw : Continuous w) {Λ : ℝ}
    (hL : ∀ x y, ‖w x - w y‖ ≤ Λ * |x - y|) (hΛ : 0 ≤ Λ) (x : ℝ) :
    Tendsto (fun M => smooth w M x) atTop (𝓝 (w x)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  set ε := η / (2 * (Λ + 1)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (Λ / (4 * ε * η))
  refine ⟨M₀, fun M hM => ?_⟩
  rw [dist_eq_norm]
  refine (smooth_err hw hL M hε x).trans_lt ?_
  have hM1 : (M₀ : ℝ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M + 1 := by positivity
  have h1 : Λ * ε < η / 2 := by
    rw [hεdef, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have h2 : Λ * (1 / (8 * ε * (M + 1))) < η / 2 := by
    rw [div_lt_iff₀ (by positivity)] at hM₀
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [mul_add]
  linarith

/-! ## Derivative bound -/
lemma supp_deriv_le {K : Set (Phase n)} (hK : IsConvexDomain K) {f : ℝ → Phase n} {f' : Phase n}
    {t c : ℝ} (hf : HasDerivAt f f' t)
    (hH : ∀ a b, a ≤ b → supp K (-J (f b - f a)) ≤ c * (b - a)) : supp K (-J f') ≤ c := by
  have hs := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left
    (nhdsWithin_mono t (s := Set.Ioi t) (fun y hy => (Set.mem_Ioi.1 hy).ne'))
  have hcl : IsClosed {v : Phase n | supp K (-J v) ≤ c} :=
    isClosed_le ((continuous_supp hK).comp continuous_J.neg) continuous_const
  refine hcl.mem_of_tendsto hs (eventually_nhdsWithin_of_forall fun y hy' => ?_)
  have hy : t < y := hy'
  simp only [Set.mem_ofPred_eq]
  rw [slope_def_module, J_smul, ← smul_neg, supp_smul K (inv_nonneg.2 (sub_nonneg.2 hy.le))]
  have := hH t y hy.le
  have hp : 0 < y - t := sub_pos.2 hy
  calc (y - t)⁻¹ * supp K (-J (f y - f t)) ≤ (y - t)⁻¹ * (c * (y - t)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = c := by field_simp

/-! ## Part W -/
theorem exists_trig_loop {n : ℕ} (hn : 1 ≤ n) {L : Set (Phase n)} (hL : IsConvexDomain L)
    (h0 : (0 : Phase n) ∈ interior L) {α : ℝ} (hα : cEHZ L < ENNReal.ofReal α) :
    ∃ (D : ℕ) (b : ℤ → Vector (Fin n)),
      ∫ t in (0 : ℝ)..1, supportFn (Capacities.Φ n '' L) (-(Complex.I • trigVel D b t)) ^ 2 <
        4 * α * trigAction D b := by
  obtain ⟨γ, hγ, -, hA, hc, -⟩ := exists_char_cEHZ_eq hn hL
  set A := action γ with hAdef
  have hAα : A < α := by
    rw [hc] at hα
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 hα).1
  have hℓ : ell L γ = 2 * A := ell_char hL hγ
  obtain ⟨r, hr, hball'⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hball : Metric.ball (0 : Phase n) r ⊆ L := hball'.trans interior_subset
  have hloop : IsLoop γ := ⟨hγ.1, isAC_of_char hγ⟩
  have hαpos : 0 < α := hA.trans hAα
  set δ₀ := 4 * A * (α - A) with hδ₀
  have hδ₀pos : 0 < δ₀ := by have := sub_pos.2 hAα; positivity
  set ε := min A (δ₀ / (20 * A)) with hεdef
  have hε : 0 < ε := lt_min hA (by positivity)
  have hεA : ε ≤ A := min_le_left _ _
  have hε2 : ε ≤ δ₀ / (20 * A) := min_le_right _ _
  set η := δ₀ / (16 * α) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨w, hwp, hwA, hwH⟩ := exists_reparam_h hL hr hball hloop hε
  set c := ell L γ + ε with hcdef
  set Λ := Real.toNNReal (2 / r * c) with hΛdef
  have hwL : LipschitzWith Λ w := lip_of_hbound hL hr hball hwH
  have hwc : Continuous w := hwL.continuous
  have hwL' : ∀ x y, ‖w x - w y‖ ≤ (Λ : ℝ) * |x - y| := fun x y => by
    have := hwL.dist_le_mul x y
    rwa [dist_eq_norm, Real.dist_eq] at this
  have hsH := smooth_hbound hL hwc hwH
  have hsL : ∀ M, LipschitzWith Λ (smooth w M) := fun M => lip_of_hbound hL hr hball (hsH M)
  have hlim := tendsto_action (fun M => smooth_periodic hwp M) hsL hwp hwL
    (tendsto_smooth hwc hwL' Λ.2)
  obtain ⟨M, hM⟩ := (hlim.eventually (lt_mem_nhds (show action w - η < action w by linarith))).exists
  refine ⟨M, smCoeff w M, ?_⟩
  set b := smCoeff w M with hb
  have hsm : smooth w M = fun t => Capacities.Ψ n (trigLoop M b t) := by
    funext t
    rw [← smooth_trig hwc hwp M t, Capacities.Ψ_Φ]
  have hact : trigAction M b = action (smooth w M) := by rw [hsm, trigAction_eq]
  have hder : ∀ t, HasDerivAt (smooth w M) (Capacities.Ψ n (trigVel M b t)) t := fun t => by
    rw [hsm]
    exact (Capacities.Ψ n).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_trigLoop M b t)
  have hrw : ∀ t, supportFn (Capacities.Φ n '' L) (-(Complex.I • trigVel M b t)) =
      supp L (-J (Capacities.Ψ n (trigVel M b t))) := fun t => by
    rw [← supportFn_Φ, map_neg, Φ_J, Capacities.Φ_Ψ]
  have hbd : ∀ t, supp L (-J (Capacities.Ψ n (trigVel M b t))) ^ 2 ≤ c ^ 2 := fun t => by
    have h1 := supp_deriv_le hL (hder t) (hsH M)
    have h2 := supp_lower0 hL hr hball (-J (Capacities.Ψ n (trigVel M b t)))
    have h3 : 0 ≤ supp L (-J (Capacities.Ψ n (trigVel M b t))) :=
      le_trans (by positivity) h2
    exact pow_le_pow_left₀ h3 h1 2
  have hcont : Continuous fun t => supp L (-J (Capacities.Ψ n (trigVel M b t))) ^ 2 :=
    ((continuous_supp hL).comp (continuous_J.comp
      ((Capacities.Ψ n).continuous.comp (continuous_trigVel M b))).neg).pow 2
  have hint : ∫ t in (0 : ℝ)..1, supportFn (Capacities.Φ n '' L)
      (-(Complex.I • trigVel M b t)) ^ 2 ≤ c ^ 2 := by
    simp only [hrw]
    have hci : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 1 := intervalIntegrable_const
    have := intervalIntegral.integral_mono_on zero_le_one (hcont.intervalIntegrable 0 1)
      hci (fun t _ => hbd t)
    simpa using this
  refine hint.trans_lt ?_
  rw [hact]
  have hM' : A - η < action (smooth w M) := by rw [hAdef, ← hwA]; exact hM
  have hc2 : c ^ 2 ≤ 4 * A ^ 2 + δ₀ / 4 := by
    rw [hcdef, hℓ]
    have : 5 * A * ε ≤ δ₀ / 4 := by
      have := mul_le_mul_of_nonneg_left hε2 (by positivity : (0 : ℝ) ≤ 5 * A)
      have e : 5 * A * (δ₀ / (20 * A)) = δ₀ / 4 := by field_simp; ring
      linarith
    nlinarith
  have h4 : 4 * α * (A - η) = 4 * A ^ 2 + δ₀ - δ₀ / 4 := by
    rw [hηdef, hδ₀]; field_simp; ring
  have h5 : 4 * α * (A - η) < 4 * α * action (smooth w M) :=
    mul_lt_mul_of_pos_left hM' (by positivity)
  linarith

end Viterbo.Cap.PartW
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

theorem solution : type_of% @Viterbo.Cap.PartW.exists_trig_loop := @Viterbo.Cap.PartW.exists_trig_loop
