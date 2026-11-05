-- Prove2me | solution 1 for Viterbo.Cap.bridge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T17:54:42.102996+00:00
-- url     : https://prove2.me/submissions/46f0aeea-2c76-415e-aee1-7b3ad6aa6561

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

 theorem form_ext {v w : Vector κ} (h : ∀ z, form v z = form w z) : v = w := by
   exact smul_right_injective _ Complex.I_ne_zero (ext_inner_right ℝ h)

 theorem injective {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) : Function.Injective A := by
   intro v w hvw
   apply form_ext
   intro z
   calc
     form v z = form (A v) (A z) := (hA v z).symm
     _ = form (A w) (A z) := by rw [hvw]
     _ = form w z := hA w z

 theorem invertible {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) : A.IsInvertible := by
   have hi := injective hA
   exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hi)
     (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hi)), rfl⟩

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

lemma pI_comm (z w : Phase n) : phaseInner z w = phaseInner w z := by
  simp [phaseInner, real_inner_comm]

lemma pI_add_left (x y w : Phase n) :
    phaseInner (x + y) w = phaseInner x w + phaseInner y w := by
  simp [phaseInner, inner_add_left]; ring

lemma pI_smul_left (c : ℝ) (x w : Phase n) :
    phaseInner (c • x) w = c * phaseInner x w := by
  simp [phaseInner, real_inner_smul_left]; ring

lemma pI_smul_right (c : ℝ) (w x : Phase n) :
    phaseInner w (c • x) = c * phaseInner w x := by
  simp [phaseInner, real_inner_smul_right]; ring

lemma pI_zero_right (x : Phase n) : phaseInner x 0 = 0 := by simp [phaseInner]

lemma J_smul (c : ℝ) (z : Phase n) : J (c • z) = c • J z := by
  simp [J]

lemma J_add (x y : Phase n) : J (x + y) = J x + J y := by
  refine Prod.ext ?_ ?_ <;> simp [J]; abel

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

/-! ### Translation -/

lemma frontier_translate (S : Set (Phase n)) (w : Phase n) :
    frontier ((· + w) '' S) = (· + w) '' frontier S :=
  ((Homeomorph.addRight w).image_frontier S).symm

lemma normalCone_translate (S : Set (Phase n)) (w z : Phase n) :
    normalCone phaseInner ((· + w) '' S) (z + w) = normalCone phaseInner S z := by
  ext u
  simp only [normalCone, mem_ofPred_eq, forall_mem_image, add_sub_add_right_eq_sub]

lemma gcc_translate {S : Set (Phase n)} {γ : ℝ → Phase n}
    (h : IsGeneralizedClosedCharacteristic S γ) (w : Phase n) :
    IsGeneralizedClosedCharacteristic ((· + w) '' S) (fun t => γ t + w) := by
  obtain ⟨hper, hfr, v, hvint, hftc, hae⟩ := h
  refine ⟨fun t => by simp [hper t], fun t => ?_, v, hvint, fun a b => ?_, ?_⟩
  · rw [frontier_translate]; exact mem_image_of_mem _ (hfr t)
  · rw [← hftc a b]; exact add_sub_add_right_eq_sub _ _ _
  · filter_upwards [hae] with t ht
    rwa [normalCone_translate]

lemma action_translate {S : Set (Phase n)} {γ : ℝ → Phase n}
    (h : IsGeneralizedClosedCharacteristic S γ) (w : Phase n) :
    action (fun t => γ t + w) = action γ := by
  obtain ⟨hper, -, v, hvint, hftc, -⟩ := h
  have hf' : ∀ a b, (fun t => γ t + w) b - (fun t => γ t + w) a = ∫ s in a..b, v s := by
    intro a b; rw [← hftc a b]; exact add_sub_add_right_eq_sub _ _ _
  have hγc := cont_of_ac hvint hftc
  rw [action_eq hvint hf', action_eq hvint hftc]
  have e : ∀ t, phaseInner (J (γ t + w)) (v t) =
      phaseInner (J (γ t)) (v t) + phaseInner (J w) (v t) := fun t => by
    rw [J_add, pI_add_left]
  simp only [e]
  rw [intervalIntegral.integral_add (ii_pI (w := fun t => J (γ t)) (continuous_J.comp hγc) hvint 0 1)
    (ii_pI (w := fun _ => J w) continuous_const hvint 0 1), integral_pI_const hvint, ← hftc 0 1,
    show γ 1 = γ 0 by simpa using hper 0, sub_self, pI_zero_right, add_zero]

lemma cEHZ_translate_le (S : Set (Phase n)) (w : Phase n) :
    cEHZ ((· + w) '' S) ≤ cEHZ S := by
  refine le_iInf₂ (fun γ hγ => ?_)
  have hnc : ∃ s t, (fun t => γ t + w) s ≠ (fun t => γ t + w) t := by
    obtain ⟨s, t, hst⟩ := hγ.2
    exact ⟨s, t, fun h => hst (add_right_cancel h)⟩
  refine (iInf₂_le (fun t => γ t + w) ⟨gcc_translate hγ.1 w, hnc⟩).trans ?_
  rw [action_translate hγ.1 w]

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

lemma cEHZ_translate (S : Set (Phase n)) (d : Phase n) :
    cEHZ ((fun z => z + d) '' S) = cEHZ S := by
  refine le_antisymm (cEHZ_translate_le S d) ?_
  have h := cEHZ_translate_le ((· + d) '' S) (-d)
  rwa [image_image, show (fun x : Phase n => x + d + -d) = id from funext fun x => by simp,
    image_id] at h

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

end Viterbo.CM
end

section
set_option autoImplicit false

open scoped ENNReal ContDiff Pointwise

namespace Viterbo.Capacities

open OAI.SymmetricPolar Set Topology

/-! ## Generic facts about symplectic embeddings -/

/-- For `n ≥ 1`, a symplectic embedding is differentiable at every point of its domain. -/
theorem differentiableAt_of_symp {n : ℕ} (hn : 1 ≤ n) {e : Phase n → Phase n} {z : Phase n}
    (h : ∀ v w : Phase n, omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    DifferentiableAt ℝ e z := by
  by_contra hd
  have h0 := fderiv_zero_of_not_differentiableAt hd
  let x : Position n := EuclideanSpace.single ⟨0, hn⟩ 1
  have := h (x, 0) (0, x)
  rw [h0] at this
  simp [omega0, x] at this

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

theorem norm_sq_Φ_apply {n : ℕ} (z : Phase n) (j : Fin n) :
    ‖Φ n z j‖ ^ 2 = z.1 j ^ 2 + z.2 j ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Φ_apply_apply]
  simp
  ring

theorem norm_sq_Φ {n : ℕ} (z : Phase n) : ‖Φ n z‖ ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_sq_Φ_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]

theorem form_Φ {n : ℕ} (x y : Phase n) :
    OAI.ComplexSymplectic.form (Φ n x) (Φ n y) = omega0 x y := by
  simp only [OAI.ComplexSymplectic.form, omega0, real_inner_eq_re_inner, PiLp.inner_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Φ_apply_apply, inner]
  ring

theorem norm_sq_Ψ {n : ℕ} (w : OAI.FourierPolynomial.Vector (Fin n)) : ‖(Ψ n w).1‖ ^ 2 + ‖(Ψ n w).2‖ ^ 2 = ‖w‖ ^ 2 := by
  rw [← norm_sq_Φ, Φ_Ψ]

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

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartA1
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
theorem isConvexDomain_affinity {n : ℕ} {S : Set (Phase n)} (hS : IsConvexDomain S)
    (d : Phase n) {a : ℝ} (ha : a ≠ 0) : IsConvexDomain ((fun x => d + a • x) '' S) := by
  obtain ⟨hb, hc, hi⟩ := hS
  refine ⟨?_, hc.affinity d a, ?_⟩
  · obtain ⟨R, hR⟩ := hb.exists_norm_le
    refine isBounded_iff_forall_norm_le.mpr ⟨‖d‖ + ‖a‖ * R, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    calc ‖d + a • x‖ ≤ ‖d‖ + ‖a • x‖ := norm_add_le _ _
      _ = ‖d‖ + ‖a‖ * ‖x‖ := by rw [norm_smul]
      _ ≤ ‖d‖ + ‖a‖ * R := by gcongr; exact hR x hx
  · let h : Phase n ≃ₜ Phase n := (Homeomorph.smulOfNeZero a ha).trans (Homeomorph.addLeft d)
    have hh : ∀ x, h x = d + a • x := fun x => rfl
    obtain ⟨x, hx⟩ := hi
    refine ⟨h x, ?_⟩
    have : (fun x => d + a • x) '' S = h '' S := by
      ext y; simp only [mem_image, hh]
    rw [this, ← h.image_interior]
    exact mem_image_of_mem _ hx

theorem cEHZ_affinity {n : ℕ} (S : Set (Phase n)) (d : Phase n) {a : ℝ} (ha : 0 < a) :
    cEHZ ((fun x => d + a • x) '' S) = ENNReal.ofReal (a ^ 2) * cEHZ S := by
  have : (fun x => d + a • x) '' S = (fun z => z + d) '' (a • S) := by
    rw [← Set.image_smul, image_image]
    exact image_congr fun x _ => add_comm _ _
  rw [this, Viterbo.CM.cEHZ_translate, Viterbo.CM.cEHZ_smul _ ha]

theorem gauge_preimage_Ψ {n : ℕ} (S : Set (Phase n)) (u : Phase n) :
    gauge (Capacities.Ψ n ⁻¹' S) (Capacities.Φ n u) = gauge S u := by
  unfold gauge
  congr 1
  ext r
  simp only [mem_ofPred_eq]
  refine and_congr_right fun hr => ?_
  rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne', mem_smul_set_iff_inv_smul_mem₀ hr.ne', mem_preimage,
    map_smul, Capacities.Ψ_Φ]

theorem norm_Ψ_le {n : ℕ} (w : Vector (Fin n)) : ‖Capacities.Ψ n w‖ ≤ ‖w‖ := by
  have h := Capacities.norm_sq_Ψ w
  rw [Prod.norm_def]
  have h1 := norm_nonneg (Capacities.Ψ n w).1
  have h2 := norm_nonneg (Capacities.Ψ n w).2
  have h3 := norm_nonneg w
  refine max_le ?_ ?_ <;> nlinarith

theorem bridge {n : ℕ} (hn : 1 ≤ n) {K L : Set (Phase n)} (hK : IsConvexDomain K)
    (hL : IsConvexDomain L) (he : HasSymplecticEmbedding K L) {η : ℝ} (hη : 0 < η) :
    ∃ (K' L' : Set (Vector (Fin n))) (r : ℝ) (e : OpenPartialHomeomorph (Vector (Fin n)) (Vector (Fin n))),
      Body K' r ∧ IsConvexDomain (Capacities.Ψ n '' K') ∧
      cEHZ (Capacities.Ψ n '' K') = cEHZ K ∧
      IsConvexDomain (Capacities.Ψ n '' L') ∧ (0 : Phase n) ∈ interior (Capacities.Ψ n '' L') ∧
      cEHZ (Capacities.Ψ n '' L') = ENNReal.ofReal ((1 + η) ^ 2) * cEHZ L ∧
      e.source = interior K' ∧ (0 : Vector (Fin n)) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧
      (∀ w ∈ e.source, OAI.ComplexSymplectic.Preserves (fderiv ℝ e w)) ∧
      ∃ θ : ℝ, θ < 1 ∧ ∀ w ∈ e.source, gauge L' (e w) ≤ θ := by
  obtain ⟨E, hcd, hemb, hmaps, hsymp⟩ := he
  set Φ := Capacities.Φ n with hΦdef
  set Ψ := Capacities.Ψ n with hΨdef
  have hΨΦ : ∀ z, Ψ (Φ z) = z := Capacities.Ψ_Φ
  have hΦΨ : ∀ w, Φ (Ψ w) = w := Capacities.Φ_Ψ
  have hΨsurj : Function.Surjective Ψ := fun x => ⟨Φ x, hΨΦ x⟩
  have hΦinj : Function.Injective Φ := fun x y h => by
    have := congrArg Ψ h; rwa [hΨΦ, hΨΦ] at this
  have hΨinj : Function.Injective Ψ := fun x y h => by
    have := congrArg Φ h; rwa [hΦΨ, hΦΨ] at this
  -- centre and radius
  obtain ⟨c, hc⟩ := hK.2.2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  have hcK : c ∈ K := interior_subset hc
  -- K side
  set K₀ : Set (Phase n) := (fun x => -c + (1 : ℝ) • x) '' K with hK₀
  have hK₀cd : IsConvexDomain K₀ := isConvexDomain_affinity hK (-c) one_ne_zero
  set K' : Set (Vector (Fin n)) := Ψ ⁻¹' K₀ with hK'
  have hΨK' : Ψ '' K' = K₀ := image_preimage_eq _ hΨsurj
  have memK' : ∀ w, w ∈ K' ↔ Ψ w + c ∈ K := by
    intro w
    constructor
    · rintro ⟨y, hy, hyw⟩
      have : Ψ w + c = y := by simp only [one_smul] at hyw; rw [← hyw]; abel
      rw [this]; exact hy
    · intro h
      exact ⟨Ψ w + c, h, by simp only [one_smul]; abel⟩
  have hBody : Body K' r := by
    refine ⟨hK₀cd.2.1.linear_preimage (Ψ : Vector (Fin n) →ₗ[ℝ] Phase n), ?_, hr, ?_⟩
    · obtain ⟨R, hR⟩ := hK₀cd.1.exists_norm_le
      refine isBounded_iff_forall_norm_le.mpr ⟨‖Φ‖ * R, fun w hw => ?_⟩
      calc ‖w‖ = ‖Φ (Ψ w)‖ := by rw [hΦΨ]
        _ ≤ ‖Φ‖ * ‖Ψ w‖ := Φ.le_opNorm _
        _ ≤ ‖Φ‖ * R := by gcongr; exact hR _ hw
    · intro w hw
      rw [memK']
      apply interior_subset
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact (norm_Ψ_le w).trans_lt hw
  have h0K' : (0 : Vector (Fin n)) ∈ interior K' :=
    interior_maximal hBody.ball Metric.isOpen_ball (Metric.mem_ball_self hr)
  -- L side
  set p := E c with hp
  have hpL : p ∈ L := hmaps hcK
  set M₀ : Set (Phase n) := (fun x => -p + (1 : ℝ) • x) '' L with hM₀
  have hM₀cd : IsConvexDomain M₀ := isConvexDomain_affinity hL (-p) one_ne_zero
  have h0M₀ : (0 : Phase n) ∈ M₀ := ⟨p, hpL, by simp only [one_smul]; abel⟩
  obtain ⟨x₀, hx₀⟩ := hM₀cd.2.2
  set L'' : Set (Phase n) := AffineMap.homothety x₀ (1 + η) '' M₀ with hL''
  have hL''eq : L'' = (fun x => (x₀ - (1 + η) • x₀) + (1 + η) • x) '' M₀ := by
    refine image_congr fun x _ => ?_
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub]
    abel
  have hL''cd : IsConvexDomain L'' := by
    rw [hL''eq]; exact isConvexDomain_affinity hM₀cd _ (by linarith)
  have hclos : closure M₀ ⊆ interior L'' :=
    hM₀cd.2.1.closure_subset_interior_image_homothety_of_one_lt hx₀ (1 + η) (by linarith)
  have h0L'' : (0 : Phase n) ∈ interior L'' := hclos (subset_closure h0M₀)
  set L' : Set (Vector (Fin n)) := Ψ ⁻¹' L'' with hL'
  have hΨL' : Ψ '' L' = L'' := image_preimage_eq _ hΨsurj
  have hcEHZL : cEHZ L'' = ENNReal.ofReal ((1 + η) ^ 2) * cEHZ L := by
    rw [hL''eq, cEHZ_affinity _ _ (by linarith), hM₀, cEHZ_affinity _ _ one_pos]
    simp
  -- θ
  have hCc : IsCompact (closure M₀) := hM₀cd.1.isCompact_closure
  have hgc : Continuous (gauge L'') :=
    continuous_gauge hL''cd.2.1 (mem_interior_iff_mem_nhds.mp h0L'')
  obtain ⟨u₀, hu₀, hmax⟩ := hCc.exists_isMaxOn ⟨0, subset_closure h0M₀⟩ hgc.continuousOn
  have hθ : gauge L'' u₀ < 1 := interior_subset_gauge_lt_one _ (hclos hu₀)
  -- the map
  set U : Set (Vector (Fin n)) := interior K' with hU
  let f : Vector (Fin n) → Vector (Fin n) := fun w => Φ (E (Ψ w + c)) - Φ p
  have hmapsU : MapsTo (fun w => Ψ w + c) U K := fun w hw => (memK' w).mp (interior_subset hw)
  have hf : ContDiffOn ℝ ∞ f U := by
    refine (Φ.contDiff.comp_contDiffOn
      (hcd.comp (Ψ.contDiff.add contDiff_const).contDiffOn hmapsU)).sub contDiffOn_const
  have hi : InjOn f U := by
    intro w₁ h₁ w₂ h₂ h
    have h' : E (Ψ w₁ + c) = E (Ψ w₂ + c) := hΦinj (sub_left_injective h)
    have h'' := hemb.injective (a₁ := ⟨_, hmapsU h₁⟩) (a₂ := ⟨_, hmapsU h₂⟩) h'
    have : Ψ w₁ = Ψ w₂ := add_right_cancel (congrArg Subtype.val h'')
    exact hΨinj this
  have hfd : ∀ w ∈ U, fderiv ℝ f w =
      Φ.comp ((fderiv ℝ E (Ψ w + c)).comp Ψ) := by
    intro w hw
    have hz := hmapsU hw
    have hE := (Capacities.differentiableAt_of_symp hn (hsymp _ hz)).hasFDerivAt
    have hin : HasFDerivAt (fun w => Ψ w + c) Ψ w := Ψ.hasFDerivAt.add_const c
    exact ((Φ.hasFDerivAt.comp w (hE.comp w hin)).sub_const (Φ p)).fderiv
  have hpres : ∀ w ∈ U, OAI.ComplexSymplectic.Preserves (fderiv ℝ f w) := by
    intro w hw v u
    rw [hfd w hw]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hΦdef, Capacities.form_Φ, hsymp _ (hmapsU hw), ← Capacities.form_Φ, Capacities.Φ_Ψ,
      Capacities.Φ_Ψ]
  have hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible := fun x hx =>
    OAI.ComplexSymplectic.invertible (hpres x hx)
  let e := OAI.EmbeddingInverse.localEquiv isOpen_interior f hf hi hD
  have hecoe : (e : Vector (Fin n) → Vector (Fin n)) = f := rfl
  refine ⟨K', L', r, e, hBody, ?_, ?_, ?_, ?_, ?_, rfl, h0K', ?_, ?_, ?_, gauge L'' u₀, hθ, ?_⟩
  · rw [hΨK']; exact hK₀cd
  · rw [hΨK', hK₀, show (fun x : Phase n => -c + (1 : ℝ) • x) = fun x => x + -c from
      funext fun x => by rw [one_smul, add_comm]]
    exact Viterbo.CM.cEHZ_translate K (-c)
  · rw [hΨL']; exact hL''cd
  · rw [hΨL']; exact h0L''
  · rw [hΨL']; exact hcEHZL
  · rw [hecoe]
    show Φ (E (Ψ 0 + c)) - Φ p = 0
    rw [map_zero, zero_add, sub_self]
  · rw [hecoe]; exact hf
  · rw [hecoe]; exact hpres
  · intro w hw
    rw [hecoe]
    have hz := hmapsU hw
    have hu : -p + (1 : ℝ) • E (Ψ w + c) ∈ M₀ := ⟨_, hmaps hz, rfl⟩
    have : f w = Φ (-p + (1 : ℝ) • E (Ψ w + c)) := by
      simp only [f, one_smul, map_add, map_neg]; abel
    rw [this, hL', hΦdef, hΨdef, gauge_preimage_Ψ]
    exact hmax (subset_closure hu)

end Viterbo.Cap.PartA1
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part A1: the bridge from a symplectic embedding of convex domains -/

/-! ## Part A2: one-variable profiles -/


/-! ## Part A3: monotonicity of `c_EHZ` under symplectic embeddings of convex domains -/

/-! ## Part P: the envelope capacity and the target -/

end Viterbo.Cap
end
end

theorem solution : type_of% @Viterbo.Cap.PartA1.bridge := @Viterbo.Cap.PartA1.bridge
