-- Prove2me | solution 1 for Viterbo.exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T17:54:46.768511+00:00
-- url     : https://prove2.me/submissions/ac65b763-086e-4008-9fe3-c61deff660a8

import Mathlib
import Definitions.Def_OAIQWSP000
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq
import Definitions.Def_ViterboCap
import Theorems.Thm_Viterbo_cEHZ_capacityBall
import Theorems.Thm_Viterbo_Cap_cEHZ_le_of_hse
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

lemma pI_add_left (x y w : Phase n) :
    phaseInner (x + y) w = phaseInner x w + phaseInner y w := by
  simp [phaseInner, inner_add_left]; ring

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

lemma J_add (x y : Phase n) : J (x + y) = J x + J y := by
  refine Prod.ext ?_ ?_ <;> simp [J]; abel

lemma J_sub (x y : Phase n) : J (x - y) = J x - J y := by
  refine Prod.ext ?_ ?_ <;> simp [J]; abel

lemma J_J (x : Phase n) : J (J x) = -x := by
  refine Prod.ext ?_ ?_ <;> simp [J]

lemma J_eq_zero {z : Phase n} (h : J z = 0) : z = 0 := by
  simp only [J, Prod.mk_eq_zero, neg_eq_zero] at h
  exact Prod.ext h.2 h.1

lemma pI_J_J (x y : Phase n) : phaseInner (J x) (J y) = phaseInner x y := by
  simp [phaseInner, J]; ring

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

lemma ell_eq {z v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) (K : Set (Phase n)) :
    ell K z = ∫ t in (0 : ℝ)..1, supp K (-J (v t)) := by
  unfold ell
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [deriv_ae hv hf] with t ht _
  rw [ht]; rfl

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

theorem hse_mono {n : ℕ} {U U' V V' : Set (Phase n)} (h : HasSymplecticEmbedding U V)
    (hU : U' ⊆ U) (hV : V ⊆ V') : HasSymplecticEmbedding U' V' := by
  obtain ⟨e, hcd, hemb, hmaps, hsymp⟩ := h
  refine ⟨e, hcd.mono hU, ?_, (hmaps.mono_left hU).mono_right hV, fun z hz => hsymp z (hU hz)⟩
  exact hemb.comp (IsEmbedding.inclusion hU)

theorem hse_refl {n : ℕ} (U : Set (Phase n)) : HasSymplecticEmbedding U U := by
  refine ⟨id, contDiffOn_id, IsEmbedding.subtypeVal, mapsTo_id _, ?_⟩
  intro z _ v w
  simp

theorem hse_of_subset {n : ℕ} {U V : Set (Phase n)} (h : U ⊆ V) : HasSymplecticEmbedding U V :=
  hse_mono (hse_refl U) subset_rfl h

theorem hse_trans {n : ℕ} (hn : 1 ≤ n) {U V W : Set (Phase n)} (h₁ : HasSymplecticEmbedding U V)
    (h₂ : HasSymplecticEmbedding V W) : HasSymplecticEmbedding U W := by
  obtain ⟨e₁, hcd₁, hemb₁, hmaps₁, hsymp₁⟩ := h₁
  obtain ⟨e₂, hcd₂, hemb₂, hmaps₂, hsymp₂⟩ := h₂
  refine ⟨e₂ ∘ e₁, hcd₂.comp hcd₁ hmaps₁, ?_, hmaps₂.comp hmaps₁, ?_⟩
  · exact hemb₂.comp (hemb₁.codRestrict V (fun z => hmaps₁ z.2))
  · intro z hz v w
    have hd₁ := differentiableAt_of_symp hn (hsymp₁ z hz)
    have hd₂ := differentiableAt_of_symp hn (hsymp₂ (e₁ z) (hmaps₁ hz))
    rw [fderiv_comp z hd₂ hd₁]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hsymp₂ _ (hmaps₁ hz), hsymp₁ z hz]

/-- Conjugating a symplectic embedding by a conformally symplectic linear isomorphism. -/
theorem hse_conj {n : ℕ} (L : Phase n ≃L[ℝ] Phase n) (κ : ℝ)
    (hL : ∀ v w, omega0 (L v) (L w) = κ * omega0 v w) {U V : Set (Phase n)}
    (h : HasSymplecticEmbedding U V) : HasSymplecticEmbedding (L '' U) (L '' V) := by
  obtain ⟨e, hcd, hemb, hmaps, hsymp⟩ := h
  have hmU : MapsTo L.symm (L '' U) U := by
    rintro _ ⟨u, hu, rfl⟩
    simpa using hu
  refine ⟨fun z => L (e (L.symm z)), ?_, ?_, ?_, ?_⟩
  · exact L.contDiff.comp_contDiffOn (hcd.comp L.symm.contDiff.contDiffOn hmU)
  · let g : (L '' U) ≃ₜ U :=
      { toFun := fun z => ⟨L.symm z, hmU z.2⟩
        invFun := fun u => ⟨L u, mem_image_of_mem _ u.2⟩
        left_inv := fun z => Subtype.ext (by simp)
        right_inv := fun u => Subtype.ext (by simp)
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have := L.toHomeomorph.isEmbedding.comp (hemb.comp g.isEmbedding)
    exact this
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨e u, hmaps hu, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩ v w
    have hf : (fun z => L (e (L.symm z))) = L ∘ (e ∘ L.symm) := rfl
    rw [hf, L.comp_fderiv, L.symm.comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [hL, hsymp u hu]
    have := hL (L.symm v) (L.symm w)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at this
    exact this.symm

/-- Scaling by `α`. -/
noncomputable def scaleL (n : ℕ) (α : ℝ) (hα : α ≠ 0) : Phase n ≃L[ℝ] Phase n :=
  (LinearEquiv.smulOfNeZero ℝ (Phase n) α hα).toContinuousLinearEquiv

theorem scaleL_apply (n : ℕ) (α : ℝ) (hα : α ≠ 0) (z : Phase n) : scaleL n α hα z = α • z := rfl

theorem hse_smul {n : ℕ} {α : ℝ} (hα : α ≠ 0) {U V : Set (Phase n)}
    (h : HasSymplecticEmbedding U V) : HasSymplecticEmbedding (α • U) (α • V) := by
  have key := hse_conj (scaleL n α hα) (α ^ 2) (fun v w => by
    simp only [scaleL_apply, omega0, Prod.smul_fst, Prod.smul_snd, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real]
    ring) h
  have himg : ∀ S : Set (Phase n), (scaleL n α hα) '' S = α • S := fun S => by
    rw [← Set.image_smul]; rfl
  rwa [himg, himg] at key

theorem capacityBall_subset_cylinder {n : ℕ} (c : ℝ) :
    capacityBall n c ⊆ capacityCylinder n c := by
  intro z hz i _
  simp only [capacityBall, mem_ofPred_eq] at hz
  have h1 : z.1 i ^ 2 ≤ ‖z.1‖ ^ 2 := by
    have := PiLp.norm_apply_le z.1 i
    rw [Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : z.2 i ^ 2 ≤ ‖z.2‖ ^ 2 := by
    have := PiLp.norm_apply_le z.2 i
    rw [Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have := Real.pi_pos
  nlinarith

/-! ## The bridge `ℝ²ⁿ ≅ ℂⁿ`, `(q, p) ↦ q + i p` -/


theorem isOpen_capacityBall (n : ℕ) (c : ℝ) : IsOpen (capacityBall n c) :=
  isOpen_lt (by fun_prop) continuous_const

/-! ## Non-squeezing in phase-space form -/

/-! ## The two capacities -/

/-- Conformality from the one-sided inequality. -/
theorem conformal_of_le {n : ℕ} (c : Set (Phase n) → ℝ≥0∞)
    (h : ∀ α : ℝ, 0 < α → ∀ U : Set (Phase n), c (α • U) ≤ ENNReal.ofReal (α ^ 2) * c U) :
    ∀ α : ℝ, 0 < α → ∀ U : Set (Phase n), c (α • U) = ENNReal.ofReal (α ^ 2) * c U := by
  intro α hα U
  refine le_antisymm (h α hα U) ?_
  have h2 := h α⁻¹ (inv_pos.mpr hα) (α • U)
  rw [inv_smul_smul₀ hα.ne'] at h2
  calc ENNReal.ofReal (α ^ 2) * c U
      ≤ ENNReal.ofReal (α ^ 2) * (ENNReal.ofReal (α⁻¹ ^ 2) * c (α • U)) := by gcongr
    _ = ENNReal.ofReal (α ^ 2 * α⁻¹ ^ 2) * c (α • U) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ = c (α • U) := by
        rw [← mul_pow, mul_inv_cancel₀ hα.ne', one_pow, ENNReal.ofReal_one, one_mul]

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

/-! ## Part A1: the bridge from a symplectic embedding of convex domains -/

/-! ## Part A2: one-variable profiles -/


/-! ## Part A3: monotonicity of `c_EHZ` under symplectic embeddings of convex domains -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartP
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Convex domains: balls, scalings, translations -/
theorem ball_conv (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IsConvexDomain (capacityBall k c) ∧ (0 : Phase k) ∈ capacityBall k c := by
  have h0 : (0 : Phase k) ∈ capacityBall k c := by
    simp only [capacityBall, mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero, norm_zero]; simpa using hc
  refine ⟨⟨?_, ?_, ?_⟩, h0⟩
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt (c / Real.pi), fun z hz => ?_⟩
    simp only [capacityBall, mem_ofPred_eq] at hz
    have h1 : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ c / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]; linarith
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    constructor <;> apply Real.le_sqrt_of_sq_le <;> nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
  · intro z hz w hw l μ hl hμ hlμ
    simp only [capacityBall, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd] at *
    have e1 : ‖l • z.1 + μ • w.1‖ ≤ l * ‖z.1‖ + μ * ‖w.1‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul_of_nonneg hl, norm_smul_of_nonneg hμ]
    have e2 : ‖l • z.2 + μ • w.2‖ ≤ l * ‖z.2‖ + μ * ‖w.2‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul_of_nonneg hl, norm_smul_of_nonneg hμ]
    have n1 := norm_nonneg (l • z.1 + μ • w.1)
    have n2 := norm_nonneg (l • z.2 + μ • w.2)
    have f1 : ‖l • z.1 + μ • w.1‖ ^ 2 ≤ (l * ‖z.1‖ + μ * ‖w.1‖) ^ 2 := pow_le_pow_left₀ n1 e1 2
    have f2 : ‖l • z.2 + μ • w.2‖ ^ 2 ≤ (l * ‖z.2‖ + μ * ‖w.2‖) ^ 2 := pow_le_pow_left₀ n2 e2 2
    have g : (l * ‖z.1‖ + μ * ‖w.1‖) ^ 2 + (l * ‖z.2‖ + μ * ‖w.2‖) ^ 2 ≤
        l * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) + μ * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2) := by
      have : μ = 1 - l := by linarith
      subst this
      nlinarith [mul_nonneg hl hμ, mul_nonneg (mul_nonneg hl hμ) (sq_nonneg (‖z.1‖ - ‖w.1‖)),
        mul_nonneg (mul_nonneg hl hμ) (sq_nonneg (‖z.2‖ - ‖w.2‖))]
    have hlt : l * (Real.pi * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) + μ * (Real.pi * (‖w.1‖ ^ 2 + ‖w.2‖ ^ 2)) < c := by
      rcases hl.eq_or_lt with rfl | hl'
      · have : μ = 1 := by linarith
        subst this; linarith
      · nlinarith
    nlinarith [Real.pi_pos]
  · have hopen : IsOpen (capacityBall k c) := isOpen_lt (by fun_prop) continuous_const
    rw [hopen.interior_eq]; exact ⟨0, h0⟩

theorem isConvexDomain_smul {n : ℕ} {K : Set (Phase n)} (hK : IsConvexDomain K) {α : ℝ}
    (hα : α ≠ 0) : IsConvexDomain (α • K) :=
  ⟨hK.1.smul₀ α, hK.2.1.smul α, by rw [interior_smul₀ hα]; exact hK.2.2.smul_set⟩

/-! ## The envelope -/
/-- The envelope capacity `c(U) = ⨆ {cEHZ K : K convex domain, K ↪ U}`. -/
def capE (n : ℕ) (U : Set (Phase n)) : ℝ≥0∞ :=
  ⨆ (K : Set (Phase n)) (_ : IsConvexDomain K ∧ HasSymplecticEmbedding K U), cEHZ K

theorem le_capE {n : ℕ} {K U : Set (Phase n)} (hK : IsConvexDomain K)
    (h : HasSymplecticEmbedding K U) : cEHZ K ≤ capE n U :=
  le_iSup₂ (f := fun (K : Set (Phase n)) (_ : IsConvexDomain K ∧ HasSymplecticEmbedding K U) =>
    cEHZ K) K ⟨hK, h⟩

theorem capE_mono {n : ℕ} (hn : 1 ≤ n) {U V : Set (Phase n)} (h : HasSymplecticEmbedding U V) :
    capE n U ≤ capE n V :=
  iSup₂_le fun K hK => le_capE hK.1 (Viterbo.Capacities.hse_trans hn hK.2 h)

theorem capE_smul_le {n : ℕ} (α : ℝ) (hα : 0 < α) (U : Set (Phase n)) :
    capE n (α • U) ≤ ENNReal.ofReal (α ^ 2) * capE n U := by
  refine iSup₂_le fun K hK => ?_
  have hK1 : IsConvexDomain (α⁻¹ • K) := isConvexDomain_smul hK.1 (inv_ne_zero hα.ne')
  have hK2 : HasSymplecticEmbedding (α⁻¹ • K) U := by
    have := Viterbo.Capacities.hse_smul (inv_ne_zero hα.ne') hK.2
    rwa [inv_smul_smul₀ hα.ne'] at this
  calc cEHZ K = cEHZ (α • (α⁻¹ • K)) := by rw [smul_inv_smul₀ hα.ne']
    _ = ENNReal.ofReal (α ^ 2) * cEHZ (α⁻¹ • K) := Viterbo.CM.cEHZ_smul _ hα
    _ ≤ _ := by gcongr; exact le_capE hK1 hK2

theorem capE_eq {n : ℕ} (hn : 1 ≤ n) {K : Set (Phase n)} (hK : IsConvexDomain K) :
    capE n K = cEHZ K :=
  le_antisymm (iSup₂_le fun L hL => cEHZ_le_of_hse hn hL.1 hK hL.2)
    (le_capE hK (Viterbo.Capacities.hse_refl K))

/-! ## The circle in the `(q₁, p₁)` plane -/
/-- The basis vector at coordinate `0`. -/
def e0 (n : ℕ) (hn : 1 ≤ n) : Position n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)

theorem e0_apply {n : ℕ} (hn : 1 ≤ n) (i : Fin n) (hi : i.val = 0) : e0 n hn i = 1 := by
  have : i = ⟨0, hn⟩ := Fin.ext hi
  subst this; simp [e0]

theorem inner_e0 {n : ℕ} (hn : 1 ≤ n) (v : Position n) :
    inner (𝕜 := ℝ) (e0 n hn) v = v ⟨0, hn⟩ := by
  simp [e0, EuclideanSpace.inner_single_left]

theorem norm_e0 {n : ℕ} (hn : 1 ≤ n) : ‖e0 n hn‖ = 1 := by
  simp [e0]

/-- The loop `t ↦ (cos 2πt · e₀, sin 2πt · e₀)`. -/
def circ (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : Phase n :=
  (Real.cos (2 * Real.pi * t) • e0 n hn, Real.sin (2 * Real.pi * t) • e0 n hn)

/-- Its velocity. -/
def circV (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : Phase n :=
  ((-(2 * Real.pi * Real.sin (2 * Real.pi * t))) • e0 n hn,
    (2 * Real.pi * Real.cos (2 * Real.pi * t)) • e0 n hn)

theorem hasDerivAt_circ {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (circ n hn) (circV n hn t) t := by
  have hc : HasDerivAt (fun t => Real.cos (2 * Real.pi * t))
      (-(2 * Real.pi * Real.sin (2 * Real.pi * t))) t := by
    have := ((hasDerivAt_id t).const_mul (2 * Real.pi)).cos
    convert this using 1 <;> simp; ring
  have hs : HasDerivAt (fun t => Real.sin (2 * Real.pi * t))
      (2 * Real.pi * Real.cos (2 * Real.pi * t)) t := by
    have := ((hasDerivAt_id t).const_mul (2 * Real.pi)).sin
    convert this using 1 <;> simp; ring
  exact (hc.smul_const (e0 n hn)).prodMk (hs.smul_const (e0 n hn))

theorem continuous_circV {n : ℕ} (hn : 1 ≤ n) : Continuous (circV n hn) := by
  unfold circV; fun_prop

theorem circ_periodic {n : ℕ} (hn : 1 ≤ n) : Function.Periodic (circ n hn) 1 := by
  intro t
  simp only [circ, mul_add, mul_one, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem norm_circ_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : ‖circ n hn t‖ ≤ 1 := by
  rw [norm_prod_le_iff]
  simp only [circ, norm_smul, norm_e0, mul_one, Real.norm_eq_abs]
  exact ⟨Real.abs_cos_le_one _, Real.abs_sin_le_one _⟩

/-- The truncated cylinder. -/
def truncCyl (n : ℕ) (R : ℝ) : Set (Phase n) :=
  capacityCylinder n Real.pi ∩ Metric.ball 0 R

theorem convex_capacityCylinder (n : ℕ) : Convex ℝ (capacityCylinder n Real.pi) := by
  intro z hz w hw l μ hl hμ hlμ i hi
  have h1 := hz i hi
  have h2 := hw i hi
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  have hp := Real.pi_pos
  have a1 : z.1 i ^ 2 + z.2 i ^ 2 < 1 := by
    by_contra h; push Not at h; nlinarith
  have a2 : w.1 i ^ 2 + w.2 i ^ 2 < 1 := by
    by_contra h; push Not at h; nlinarith
  have hm : μ = 1 - l := by linarith
  subst hm
  have key : (l * z.1 i + (1 - l) * w.1 i) ^ 2 + (l * z.2 i + (1 - l) * w.2 i) ^ 2 < 1 := by
    have e : (l * z.1 i + (1 - l) * w.1 i) ^ 2 + (l * z.2 i + (1 - l) * w.2 i) ^ 2 =
        l * (z.1 i ^ 2 + z.2 i ^ 2) + (1 - l) * (w.1 i ^ 2 + w.2 i ^ 2) -
          l * (1 - l) * ((z.1 i - w.1 i) ^ 2 + (z.2 i - w.2 i) ^ 2) := by ring
    rw [e]
    have : 0 ≤ l * (1 - l) * ((z.1 i - w.1 i) ^ 2 + (z.2 i - w.2 i) ^ 2) := by positivity
    rcases hl.eq_or_lt with rfl | hl'
    · nlinarith
    · nlinarith
  nlinarith

theorem isConvexDomain_truncCyl (n : ℕ) {R : ℝ} (hR : 0 < R) :
    IsConvexDomain (truncCyl n R) := by
  refine ⟨Metric.isBounded_ball.subset inter_subset_right,
    (convex_capacityCylinder n).inter (convex_ball _ _), ?_⟩
  have hsub : capacityBall n Real.pi ∩ Metric.ball 0 R ⊆ truncCyl n R :=
    inter_subset_inter_left _ (Viterbo.Capacities.capacityBall_subset_cylinder _)
  refine ⟨0, interior_mono hsub ?_⟩
  rw [((Viterbo.Capacities.isOpen_capacityBall n _).inter Metric.isOpen_ball).interior_eq]
  exact ⟨(ball_conv n Real.pi_pos).2, Metric.mem_ball_self hR⟩

theorem circ_mem_frontier {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 1 < R) (t : ℝ) :
    circ n hn t ∈ frontier (truncCyl n R) := by
  refine ⟨?_, fun h => ?_⟩
  · have hT : Tendsto (fun r : ℝ => r • circ n hn t) (𝓝[<] 1) (𝓝 (circ n hn t)) := by
      have := ((continuous_id.smul continuous_const).tendsto' (1 : ℝ) (1 • circ n hn t) rfl)
      rw [one_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [circ, Prod.smul_fst, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul,
        e0_apply hn i hi, mul_one]
      have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
      have hp := Real.pi_pos
      have : r ^ 2 < 1 := by nlinarith [hr.1, hr.2]
      have e : (r * Real.cos (2 * Real.pi * t)) ^ 2 + (r * Real.sin (2 * Real.pi * t)) ^ 2 = r ^ 2 := by
        linear_combination r ^ 2 * hcs
      rw [e]; nlinarith
    · rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
      have := norm_circ_le hn t
      nlinarith [hr.1, hr.2, norm_nonneg (circ n hn t)]
  · have h1 := (interior_subset h).1 ⟨0, hn⟩ rfl
    simp only [circ, PiLp.smul_apply, smul_eq_mul, e0_apply hn ⟨0, hn⟩ rfl, mul_one] at h1
    have hcs : Real.cos (2 * Real.pi * t) ^ 2 + Real.sin (2 * Real.pi * t) ^ 2 = 1 := by
      linarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t)]
    rw [hcs, mul_one] at h1
    exact lt_irrefl _ h1

theorem circ_normal {n : ℕ} (hn : 1 ≤ n) (R : ℝ) (t : ℝ) :
    (2 * Real.pi) • circ n hn t ∈ normalCone phaseInner (truncCyl n R) (circ n hn t) := by
  intro y hy
  have h1 := hy.1 ⟨0, hn⟩ rfl
  simp only [phaseInner, circ, Prod.smul_fst, Prod.smul_snd, inner_sub_right, smul_smul,
    inner_smul_left, inner_smul_right, inner_e0, RCLike.conj_to_real, real_inner_self_eq_norm_sq,
    norm_e0, PiLp.smul_apply, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
  have hp := Real.pi_pos
  have h2 : y.1 ⟨0, hn⟩ ^ 2 + y.2 ⟨0, hn⟩ ^ 2 < 1 := by
    by_contra h; push Not at h; nlinarith
  nlinarith [sq_nonneg (Real.cos (2 * Real.pi * t) - y.1 ⟨0, hn⟩),
    sq_nonneg (Real.sin (2 * Real.pi * t) - y.2 ⟨0, hn⟩)]

theorem action_circ {n : ℕ} (hn : 1 ≤ n) : Viterbo.action (circ n hn) = Real.pi := by
  have hd : deriv (circ n hn) = circV n hn := funext fun t => (hasDerivAt_circ hn t).deriv
  have hi : ∀ t, phaseInner (J (circ n hn t)) (circV n hn t) = 2 * Real.pi := by
    intro t
    simp only [phaseInner, J, circ, circV, inner_neg_left, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, real_inner_self_eq_norm_sq, norm_e0]
    have hcs := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
    linear_combination (2 * Real.pi) * hcs
  unfold Viterbo.action
  rw [hd]
  simp only [hi, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]
  ring

theorem isGCC_circ {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 1 < R) :
    IsGeneralizedClosedCharacteristic (truncCyl n R) (circ n hn) := by
  refine ⟨circ_periodic hn, circ_mem_frontier hn hR, circV n hn,
    (continuous_circV hn).locallyIntegrable, fun a b => ?_, Eventually.of_forall fun t => ?_⟩
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_circ hn x)
      ((continuous_circV hn).intervalIntegrable _ _)]
  · refine ⟨(2 * Real.pi) • circ n hn t, circ_normal hn R t, ?_⟩
    simp only [J, circ, circV, Prod.smul_fst, Prod.smul_snd, smul_smul, neg_smul]

theorem circ_nonconst {n : ℕ} (hn : 1 ≤ n) : ∃ s t, circ n hn s ≠ circ n hn t := by
  refine ⟨0, 1 / 2, fun h => ?_⟩
  have := congrArg (fun z : Phase n => z.1 ⟨0, hn⟩) h
  simp only [circ, PiLp.smul_apply, smul_eq_mul, e0_apply hn ⟨0, hn⟩ rfl, mul_one] at this
  have h2 : 2 * Real.pi * (1 / 2) = Real.pi := by ring
  rw [mul_zero, Real.cos_zero, h2, Real.cos_pi] at this
  norm_num at this

theorem cEHZ_truncCyl_le {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 1 < R) :
    cEHZ (truncCyl n R) ≤ ENNReal.ofReal Real.pi := by
  refine (iInf₂_le (circ n hn) ⟨isGCC_circ hn hR, circ_nonconst hn⟩).trans ?_
  rw [action_circ hn, abs_of_pos Real.pi_pos]

/-! ## Convex domains embedded in the cylinder -/
theorem shrink_le {n : ℕ} (hn : 1 ≤ n) {K : Set (Phase n)} (hK : IsConvexDomain K)
    (he : HasSymplecticEmbedding K (capacityCylinder n Real.pi)) {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) : ENNReal.ofReal (l ^ 2) * cEHZ K ≤ ENNReal.ofReal Real.pi := by
  obtain ⟨c₀, hc₀⟩ := hK.2.2
  obtain ⟨e, hcd, hemb, hmaps, hsymp⟩ := he
  set d : Phase n := (1 - l) • c₀ with hd
  set Kl : Set (Phase n) := (fun z => z + d) '' (l • K) with hKl
  set M : Set (Phase n) := (fun z => z + d) '' (l • closure K) with hM
  have hKlM : Kl ⊆ M := image_mono (smul_set_mono subset_closure)
  have hMK : M ⊆ K := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine interior_subset (hK.2.1.openSegment_interior_closure_subset_interior hc₀ hx
      ⟨1 - l, l, by linarith, hl0, by ring, ?_⟩)
    simp only [hd, smul_eq_mul]
    exact add_comm _ _
  have hMc : IsCompact M :=
    (hK.1.isCompact_closure.smul l).image (continuous_add_const d)
  have hEc : IsCompact (e '' M) := hMc.image_of_continuousOn (hcd.continuousOn.mono hMK)
  obtain ⟨R0, hR0⟩ := isBounded_iff_forall_norm_le.1 hEc.isBounded
  set R : ℝ := max R0 1 + 1 with hR
  have hR1 : 1 < R := by have := le_max_right R0 1; linarith
  have hKlconv : IsConvexDomain Kl := by
    refine ⟨hMc.isBounded.subset hKlM, ?_, ?_⟩
    · have : (fun z : Phase n => z + d) = (fun z => d + z) := funext fun z => add_comm _ _
      rw [hKl, this]
      exact (hK.2.1.smul l).translate d
    · rw [hKl, show (fun z : Phase n => z + d) = Homeomorph.addRight d from rfl,
        ← Homeomorph.image_interior, interior_smul₀ hl0.ne']
      exact (hK.2.2.smul_set).image _
  have hKlK : Kl ⊆ K := hKlM.trans hMK
  have hemb' : HasSymplecticEmbedding Kl (truncCyl n R) := by
    refine ⟨e, hcd.mono hKlK, hemb.comp (Topology.IsEmbedding.inclusion hKlK), fun z hz => ?_,
      fun z hz => hsymp z (hKlK hz)⟩
    refine ⟨hmaps (hKlK hz), ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    have := hR0 (e z) ⟨z, hKlM hz, rfl⟩
    have := le_max_left R0 1
    linarith
  have h1 : cEHZ Kl = ENNReal.ofReal (l ^ 2) * cEHZ K := by
    rw [hKl, Viterbo.CM.cEHZ_translate, Viterbo.CM.cEHZ_smul _ hl0]
  rw [← h1]
  exact (cEHZ_le_of_hse hn hKlconv (isConvexDomain_truncCyl n (by linarith)) hemb').trans
    (cEHZ_truncCyl_le hn hR1)

theorem cEHZ_le_of_cyl {n : ℕ} (hn : 1 ≤ n) {K : Set (Phase n)} (hK : IsConvexDomain K)
    (he : HasSymplecticEmbedding K (capacityCylinder n Real.pi)) :
    cEHZ K ≤ ENNReal.ofReal Real.pi := by
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  have hat : a ≠ ⊤ := ne_top_of_lt ha
  have ht1 : a.toReal < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top ha
    simpa using this
  rcases (ENNReal.toReal_nonneg (a := a)).eq_or_lt with h0 | hpos
  · have : a = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff a).1 h0.symm with h | h
      · exact h
      · exact absurd h hat
    simp [this]
  · have hs0 : 0 < Real.sqrt a.toReal := Real.sqrt_pos.2 hpos
    have hs1 : Real.sqrt a.toReal < 1 := by
      rw [Real.sqrt_lt' one_pos]; simpa using ht1
    have := shrink_le hn hK he hs0 hs1
    rwa [Real.sq_sqrt hpos.le, ENNReal.ofReal_toReal hat] at this

/-! ## The target -/
theorem main (n : ℕ) (hn : 1 ≤ n) :
    (∃ c : Set (OAI.SymmetricPolar.Phase n) → ℝ≥0∞, IsSymplecticCapacity n c ∧
      ∀ K : Set (OAI.SymmetricPolar.Phase n), IsConvexDomain K → c K = cEHZ K) ∧
    ∀ K : Set (OAI.SymmetricPolar.Phase n), IsConvexDomain K →
      ∃ γ : ℝ → OAI.SymmetricPolar.Phase n, IsGeneralizedClosedCharacteristic K γ ∧
        (∃ s t, γ s ≠ γ t) ∧ cEHZ K = ENNReal.ofReal |Viterbo.action γ| := by
  refine ⟨⟨capE n, ⟨fun U V h => capE_mono hn h,
    Viterbo.Capacities.conformal_of_le _ capE_smul_le, ?_, ?_⟩, fun K hK => capE_eq hn hK⟩, ?_⟩
  · have hb := ball_conv n Real.pi_pos
    rw [capE_eq hn hb.1]
    have := Viterbo.cEHZ_capacityBall n hn 1 one_pos
    rwa [one_pow, mul_one] at this
  · refine le_antisymm (iSup₂_le fun K hK => cEHZ_le_of_cyl hn hK.1 hK.2) ?_
    have hb := ball_conv n Real.pi_pos
    have := Viterbo.cEHZ_capacityBall n hn 1 one_pos
    rw [one_pow, mul_one] at this
    rw [← this]
    exact le_capE hb.1 (Viterbo.Capacities.hse_of_subset
      (Viterbo.Capacities.capacityBall_subset_cylinder _))
  · intro K hK
    obtain ⟨γ, hγ, hnc, hA, hc, -⟩ := Viterbo.CM.exists_char_cEHZ_eq hn hK
    exact ⟨γ, hγ, hnc, by rw [hc, abs_of_pos hA]⟩

end Viterbo.Cap.PartP
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part P: the envelope capacity and the target -/
alias main := Viterbo.Cap.PartP.main

end Viterbo.Cap
end
end

open scoped ENNReal in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∃ c : Set (OAI.SymmetricPolar.Phase n) → ℝ≥0∞, Viterbo.IsSymplecticCapacity n c ∧
      ∀ K : Set (OAI.SymmetricPolar.Phase n), Viterbo.IsConvexDomain K → c K = Viterbo.cEHZ K) ∧
    ∀ K : Set (OAI.SymmetricPolar.Phase n), Viterbo.IsConvexDomain K →
      ∃ γ : ℝ → OAI.SymmetricPolar.Phase n, Viterbo.IsGeneralizedClosedCharacteristic K γ ∧
        (∃ s t, γ s ≠ γ t) ∧ Viterbo.cEHZ K = ENNReal.ofReal |Viterbo.action γ| :=
  Viterbo.Cap.main n hn
