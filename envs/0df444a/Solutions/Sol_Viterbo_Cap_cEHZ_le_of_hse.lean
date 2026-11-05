-- Prove2me | solution 1 for Viterbo.Cap.cEHZ_le_of_hse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T17:54:47.928481+00:00
-- url     : https://prove2.me/submissions/2a170c97-8827-4ddb-96bb-f90b9817e152

import Mathlib
import Definitions.Def_OAIQWSP000
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_Viterbo_exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq
import Definitions.Def_ViterboCap
import Theorems.Thm_Viterbo_Cap_engine
import Theorems.Thm_Viterbo_Cap_coneHyp_of_lower
import Theorems.Thm_Viterbo_Cap_exists_trig_loop
import Theorems.Thm_Viterbo_Cap_orbit_const_of_slow
import Theorems.Thm_Viterbo_Cap_bridge
universe u3 u4 u5 u6 u78 u79 u80 u81 u82 u83 u84 u85 u86 u87 u88 u89 u90 u91 u92 u93 u94 u95 u96 u97 u98 u99 u100 u101 u102 u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115 u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127

section
section
-- module Solutions.OAIQW_SymmetricPolar.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
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

 theorem zero_derivative_constant {E : Type u117} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℝ → E} (hx : ∀ t, HasDerivAt x 0 t) (s t : ℝ) : x s = x t := by
  exact is_const_of_deriv_eq_zero (fun t => (hx t).differentiableAt) (fun t => (hx t).deriv) s t

 theorem energy_constant {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) {x : ℝ → Vector κ}
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t) (s t : ℝ) : H (x s) = H (x t) := by
  apply zero_derivative_constant (x := H ∘ x) _ s t
  intro u
  have hh := ((hH.differentiable (by simp) (x u)).hasGradientAt.hasFDerivAt).comp_hasDerivAt u (hx u)
  simpa only [InnerProductSpace.toDual_apply_apply, inner_I_self] using hh

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

 theorem contDiffAt_inverse (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source)
    (hD : ∀ x ∈ e.source, (fderiv ℝ e x).IsInvertible)
    {y : E} (hy : y ∈ e.target) : ContDiffAt ℝ ∞ e.symm y := by
  have hs := he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))
  obtain ⟨D,hD⟩ := hD _ (e.map_target hy)
  apply e.contDiffAt_symm hy (f₀' := D) _ hs
  rw [hD]
  exact (hs.differentiableAt (by simp)).hasFDerivAt

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem extendFunction_apply (e : OpenPartialHomeomorph E E) (f : E → ℝ)
    {x : E} (hx : x ∈ e.source) : extendFunction e f (e x) = f x := by
  simp only [extendFunction, ite_eq_left (e.map_source hx), e.left_inv hx]

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem extendFunction_zero (e : OpenPartialHomeomorph E E) (f : E → ℝ)
    (S : Set E) (hz : ∀ x ∉ S, f x = 0) {y : E} (hy : y ∉ e '' S) :
    extendFunction e f y = 0 := by
  unfold extendFunction
  split_ifs with hyt
  · apply hz
    intro hin
    exact hy ⟨e.symm y,hin,e.right_inv hyt⟩
  · rfl

 theorem contDiff_extendFunction (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source)
    (hD : ∀ x ∈ e.source, (fderiv ℝ e x).IsInvertible)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {S : Set E} (hS : IsCompact S)
    (hSU : S ⊆ e.source) (hz : ∀ x ∉ S, f x = 0) :
    ContDiff ℝ ∞ (extendFunction e f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ e.target
  · apply (hf.contDiffAt.comp y (contDiffAt_inverse e he hD hy)).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    simp only [extendFunction, hz, ite_true, Function.comp_apply]
  · have hT : IsClosed (e '' S) := (hS.image_of_continuousOn (e.continuousOn.mono hSU)).isClosed
    have hyt : y ∈ (e '' S)ᶜ := by
      rintro ⟨x,hx,rfl⟩
      exact hy (e.map_source (hSU hx))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hT.isOpen_compl.mem_nhds hyt] with z hz'
    exact extendFunction_zero e f S hz hz'

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem extendFunction_mem_range (e : OpenPartialHomeomorph E E) (f : E → ℝ) (y : E) :
    extendFunction e f y = 0 ∨ ∃ x ∈ e.source, extendFunction e f y = f x := by
  by_cases hy : y ∈ e.target
  · exact Or.inr ⟨e.symm y,e.map_target hy, by simp only [extendFunction,hy,ite_true]⟩
  · exact Or.inl (by simp only [extendFunction,hy,ite_false])

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem eventually_of_comp (e : OpenPartialHomeomorph E E) {x : E} (hx : x ∈ e.source)
    {P : E → Prop} (hP : ∀ᶠ z in 𝓝 x, P (e z)) : ∀ᶠ y in 𝓝 (e x), P y := by
   rw [← e.map_nhds_eq hx]
   exact hP

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

 theorem form_I (v w : Vector κ) : form (Complex.I • v) w = -inner (𝕜 := ℝ) v w := by
   simp [form, smul_smul]

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

 theorem push_gradient {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) (a b : Vector κ)
    (hh : ∀ v, inner (𝕜 := ℝ) b (A v) = inner (𝕜 := ℝ) a v) :
    A (Complex.I • a) = Complex.I • b := by
   apply form_ext
   intro w
   obtain ⟨v,rfl⟩ := (LinearMap.surjective_of_injective (injective hA)) w
   change form (A (Complex.I • a)) (A v) = form (Complex.I • b) (A v)
   rw [hA, form_I, form_I, hh]

 theorem push_hamiltonian (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hω : ∀ x ∈ e.source, Preserves (fderiv ℝ e x))
    {H G : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hcomp : ∀ x ∈ e.source, H (e x) = G x) {x : Vector κ} (hx : x ∈ e.source) :
    fderiv ℝ e x (Complex.I • gradient G x) = Complex.I • gradient H (e x) := by
   apply push_gradient (hω x hx)
   intro v
   have hed := ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
   have hhd := ((hH.differentiable (by simp) (e x)).hasGradientAt.hasFDerivAt).comp x hed
   have hgd := ((hG.differentiable (by simp) x).hasGradientAt.hasFDerivAt)
   have heq : H ∘ e =ᶠ[𝓝 x] G := by
     filter_upwards [e.open_source.mem_nhds hx] with z hz
     exact hcomp z hz
   have hh := hhd.unique (hgd.congr_of_eventuallyEq heq)
   exact congrArg (fun D : Vector κ →L[ℝ] ℝ => D v) hh

 theorem inverse_curve (e : OpenPartialHomeomorph (Vector κ) (Vector κ))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hω : ∀ x ∈ e.source, Preserves (fderiv ℝ e x))
    {H G : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (hcomp : ∀ x ∈ e.source, H (e x) = G x)
    {x : ℝ → Vector κ} (hxt : ∀ t, x t ∈ e.target)
    (hx : ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t) (t : ℝ) :
    HasDerivAt (fun s => e.symm (x s)) (Complex.I • gradient G (e.symm (x t))) t := by
   let y := e.symm (x t)
   have hy : y ∈ e.source := e.map_target (hxt t)
   obtain ⟨D,hD⟩ := invertible (hω y hy)
   have hed : HasFDerivAt e D.toContinuousLinearMap y := by
     rw [hD]
     exact ((he.contDiffAt (e.open_source.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
   have hcd := (e.hasFDerivAt_symm (hxt t) hed).comp_hasDerivAt t (hx t)
   apply hcd.congr_deriv
   apply D.injective
   simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
   have hh := push_hamiltonian e he hω hH hG hcomp hy
   rw [e.right_inv (hxt t)] at hh
   change Complex.I • gradient H (x t) = D.toContinuousLinearMap (Complex.I • gradient G y)
   rw [hD]
   exact hh.symm

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem contDiffAt_homQ {r : ℝ} (hL : Body L r) {z : Vector κ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (homQ L φ) z := by
  have hn : ContDiffAt ℝ ∞ (fun z : Vector κ => ‖z‖) z := contDiffAt_norm ℝ hz
  have hinv : ContDiffAt ℝ ∞ (fun z : Vector κ => ‖z‖⁻¹) z := hn.inv (norm_ne_zero_iff.2 hz)
  exact (hn.pow 2).mul ((contDiff_mollQ φ hL).contDiffAt.comp z (hinv.smul contDiffAt_id))

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
alias contDiffAt_homQ := Viterbo.Cap.PartM.contDiffAt_homQ

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem homQ_smul {r : ℝ} (hL : Body L r) {t : ℝ} (ht : 0 ≤ t) (z : Vector κ) :
    homQ L φ (t • z) = t ^ 2 * homQ L φ z := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [homQ]
  simp only [homQ, norm_smul, Real.norm_of_nonneg ht.le, mul_inv, smul_smul]
  rw [show t⁻¹ * ‖z‖⁻¹ * t = ‖z‖⁻¹ by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]]
  ring

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
alias homQ_smul := Viterbo.Cap.PartM.homQ_smul

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem gauge_sq_le_homQ {r : ℝ} (hL : Body L r) (z : Vector κ) :
    gauge L z ^ 2 ≤ homQ L φ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [homQ, gauge_zero]
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have e : gauge L z = ‖z‖ * gauge L (‖z‖⁻¹ • z) := by
    rw [← smul_eq_mul, ← gauge_smul_of_nonneg hn.le, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [homQ, e, mul_pow]
  exact mul_le_mul_of_nonneg_left (gauge_sq_le_mollQ φ hL _) (by positivity)

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
alias gauge_sq_le_homQ := Viterbo.Cap.PartM.gauge_sq_le_homQ

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem homQ_le {r : ℝ} (hL : Body L r) (z : Vector κ) :
    homQ L φ z ≤ (gauge L z + φ.rOut * ‖z‖ / r) ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [homQ]
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have e : gauge L z = ‖z‖ * gauge L (‖z‖⁻¹ • z) := by
    rw [← smul_eq_mul, ← gauge_smul_of_nonneg hn.le, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [homQ, e]
  calc ‖z‖ ^ 2 * mollQ L φ (‖z‖⁻¹ • z)
      ≤ ‖z‖ ^ 2 * (gauge L (‖z‖⁻¹ • z) + φ.rOut / r) ^ 2 :=
        mul_le_mul_of_nonneg_left (mollQ_le φ hL _) (by positivity)
    _ = (‖z‖ * gauge L (‖z‖⁻¹ • z) + φ.rOut * ‖z‖ / r) ^ 2 := by ring

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
alias homQ_le := Viterbo.Cap.PartM.homQ_le

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
lemma differentiableAt_homQ {r : ℝ} (hL : Body L r) {z : Vector κ} (hz : z ≠ 0) :
    DifferentiableAt ℝ (homQ L φ) z :=
  (contDiffAt_homQ φ hL hz).differentiableAt (by simp)

theorem inner_gradient_homQ {r : ℝ} (hL : Body L r) {z : Vector κ} (hz : z ≠ 0) :
    inner (𝕜 := ℝ) (gradient (homQ L φ) z) z = 2 * homQ L φ z := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  have hi : HasDerivAt (fun t : ℝ => t • z) z 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const z
  have h1 : HasDerivAt (fun t : ℝ => homQ L φ (t • z)) (fderiv ℝ (homQ L φ) z z) 1 :=
    (differentiableAt_homQ φ hL hz).hasFDerivAt.comp_hasDerivAt_of_eq 1 hi (by simp)
  have h2 : HasDerivAt (fun t : ℝ => homQ L φ (t • z)) (2 * homQ L φ z) 1 := by
    have : HasDerivAt (fun t : ℝ => t ^ 2 * homQ L φ z) (2 * homQ L φ z) 1 := by
      simpa using (hasDerivAt_pow 2 (1 : ℝ)).mul_const (homQ L φ z)
    apply this.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds one_pos] with t ht
    exact homQ_smul φ hL ht.le z
  exact h1.unique h2

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
alias inner_gradient_homQ := Viterbo.Cap.PartM.inner_gradient_homQ

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem gradient_homQ_smul {r : ℝ} (hL : Body L r) {t : ℝ} (ht : 0 < t) {z : Vector κ}
    (hz : z ≠ 0) : gradient (homQ L φ) (t • z) = t • gradient (homQ L φ) z := by
  have htz : t • z ≠ 0 := smul_ne_zero ht.ne' hz
  have hfun : (fun w => homQ L φ (t • w)) = fun w => t ^ 2 * homQ L φ w :=
    funext fun w => homQ_smul φ hL ht.le w
  have hA : HasFDerivAt (fun w => homQ L φ (t • w))
      ((fderiv ℝ (homQ L φ) (t • z)).comp (t • ContinuousLinearMap.id ℝ (Vector κ))) z :=
    (differentiableAt_homQ φ hL htz).hasFDerivAt.comp z
      ((t • ContinuousLinearMap.id ℝ (Vector κ)).hasFDerivAt)
  have hB : HasFDerivAt (fun w => homQ L φ (t • w)) (t ^ 2 • fderiv ℝ (homQ L φ) z) z := by
    rw [hfun]
    exact (differentiableAt_homQ φ hL hz).hasFDerivAt.const_mul (t ^ 2)
  have hAB := hA.unique hB
  refine ext_inner_right ℝ fun v => ?_
  rw [real_inner_smul_left, gradient, gradient, InnerProductSpace.toDual_symm_apply,
    InnerProductSpace.toDual_symm_apply]
  have hv := congrArg (fun f => f v) hAB
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hv
  have : t * (fderiv ℝ (homQ L φ) (t • z) v - t * fderiv ℝ (homQ L φ) z v) = 0 := by
    linear_combination hv
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h ht.ne'
  · linarith

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
alias gradient_homQ_smul := Viterbo.Cap.PartM.gradient_homQ_smul

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
lemma continuousOn_gradient_homQ {r : ℝ} (hL : Body L r) :
    ContinuousOn (gradient (homQ L φ)) {0}ᶜ := by
  have hCD : ContDiffOn ℝ ∞ (homQ L φ) {0}ᶜ := fun z hz =>
    (contDiffAt_homQ φ hL hz).contDiffWithinAt
  have := hCD.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by simp)
  exact (InnerProductSpace.toDual ℝ (Vector κ)).symm.continuous.comp_continuousOn this

theorem norm_gradient_homQ_le {r : ℝ} (hL : Body L r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, z ≠ 0 → ‖gradient (homQ L φ) z‖ ≤ C * ‖z‖ := by
  have hS : Metric.sphere (0 : Vector κ) 1 ⊆ {0}ᶜ := by
    intro u hu h
    simp only [mem_singleton_iff] at h
    simp [h] at hu
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Vector κ) 1).exists_bound_of_continuousOn
    ((continuousOn_gradient_homQ φ hL).mono hS)
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : Vector κ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hu0 : ‖z‖⁻¹ • z ≠ 0 := smul_ne_zero (inv_ne_zero hn.ne') hz
  have e := gradient_homQ_smul φ hL hn hu0
  rw [smul_inv_smul₀ hn.ne'] at e
  rw [e, norm_smul, Real.norm_of_nonneg hn.le, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hC _ hu).trans (le_max_left _ _)) hn.le

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
alias norm_gradient_homQ_le := Viterbo.Cap.PartM.norm_gradient_homQ_le

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
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartM
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
theorem continuous_gradient_homQ {r : ℝ} (hL : Body L r) :
    Continuous (fun z => if z = 0 then (0 : Vector κ) else gradient (homQ L φ) z) := by
  obtain ⟨C, hC0, hC⟩ := norm_gradient_homQ_le φ hL
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [ContinuousAt, if_pos rfl, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun w => norm_nonneg _) (fun w => ?_)
      (?_ : Tendsto (fun w : Vector κ => C * ‖w‖) (𝓝 0) (𝓝 0))
    · split_ifs with h
      · rw [norm_zero]; positivity
      · exact hC w h
    · have : Tendsto (fun w : Vector κ => C * ‖w‖) (𝓝 0) (𝓝 (C * ‖(0 : Vector κ)‖)) :=
        ((continuous_const.mul continuous_norm).tendsto 0)
      simpa using this
  · have hev : gradient (homQ L φ) =ᶠ[𝓝 z]
        (fun w => if w = 0 then (0 : Vector κ) else gradient (homQ L φ) w) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
      have hw' : w ≠ 0 := hw
      simp [hw']
    exact ((continuousOn_gradient_homQ φ hL).continuousAt
      (isOpen_compl_singleton.mem_nhds hz)).congr hev

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
alias continuous_gradient_homQ := Viterbo.Cap.PartM.continuous_gradient_homQ

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
namespace Viterbo.Cap.PartA2
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-- The primitive of a smooth function is smooth, with derivative the function. -/
theorem primitive_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..x, g t) ∧
      ∀ x, HasDerivAt (fun x => ∫ t in a..x, g t) (g x) x := by
  have hd : ∀ x, HasDerivAt (fun x => ∫ t in a..x, g t) (g x) x := fun x =>
    (hg.continuous.integral_hasStrictDerivAt a x).hasDerivAt
  refine ⟨?_, hd⟩
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  have : deriv (fun x => ∫ t in a..x, g t) = g := funext fun x => (hd x).deriv
  rw [this]; exact hg

theorem smoothTransition_contDiff : ContDiff ℝ ∞ Real.smoothTransition :=
  Real.smoothTransition.contDiff (n := ⊤)

/-- A smooth nondecreasing profile rising from `0` (below `s₁`) to `m` (above `s₂`) with slope `< σ`,
strictly below `m` before `s₂`. -/
theorem exists_profile {s₁ s₂ σ m : ℝ} (h12 : s₁ < s₂) (hσ : 0 < σ) (hm : 0 < m)
    (hmσ : m < σ * (s₂ - s₁)) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ (∀ s, 0 ≤ deriv f s) ∧ (∀ s, deriv f s < σ) ∧
      (∀ s, s ≤ s₁ → f s = 0) ∧ (∀ s, s₂ ≤ s → f s = m) ∧ (∀ s, s < s₂ → f s < m) ∧
      (∀ s, s ≤ s₁ → deriv f s = 0) ∧ (∀ s, s₂ ≤ s → deriv f s = 0) := by
  have hmσ' : m / σ < s₂ - s₁ := by rw [div_lt_iff₀ hσ]; linarith
  set τ : ℝ := (s₂ - s₁ - m / σ) / 4 with hτdef
  have hτ : 0 < τ := by rw [hτdef]; linarith
  set χ : ℝ → ℝ := fun s => Real.smoothTransition ((s - s₁) / τ) *
    Real.smoothTransition ((s₂ - s) / τ) with hχdef
  have hχc : ContDiff ℝ ∞ χ := by
    refine (smoothTransition_contDiff.comp ?_).mul (smoothTransition_contDiff.comp ?_)
    · exact (contDiff_id.sub contDiff_const).div_const _
    · exact (contDiff_const.sub contDiff_id).div_const _
  have hχcont : Continuous χ := hχc.continuous
  have hχi : ∀ a b, IntervalIntegrable χ volume a b := fun a b => hχcont.intervalIntegrable a b
  have hχ0 : ∀ s, 0 ≤ χ s := fun s =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hχ1 : ∀ s, χ s ≤ 1 := fun s =>
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)
  have hχlo : ∀ s, s ≤ s₁ → χ s = 0 := by
    intro s hs
    simp only [hχdef]
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hτ.le),
      zero_mul]
  have hχhi : ∀ s, s₂ ≤ s → χ s = 0 := by
    intro s hs
    simp only [hχdef]
    rw [Real.smoothTransition.zero_of_nonpos (x := (s₂ - s) / τ)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hτ.le), mul_zero]
  have hχpos : ∀ s, s₁ < s → s < s₂ → 0 < χ s := by
    intro s h1 h2
    exact mul_pos (Real.smoothTransition.pos_of_pos (div_pos (by linarith) hτ))
      (Real.smoothTransition.pos_of_pos (div_pos (by linarith) hτ))
  have hχmid : ∀ s, s₁ + τ ≤ s → s ≤ s₂ - τ → χ s = 1 := by
    intro s h1 h2
    simp only [hχdef]
    rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hτ]; linarith),
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hτ]; linarith), mul_one]
  set I : ℝ := ∫ t in s₁..s₂, χ t with hIdef
  have hI : s₂ - s₁ - 2 * τ ≤ I := by
    have hs1 : s₁ ≤ s₁ + τ := by linarith
    have hs2 : s₁ + τ ≤ s₂ - τ := by rw [hτdef]; linarith [div_pos hm hσ]
    have hs3 : s₂ - τ ≤ s₂ := by linarith
    rw [hIdef, ← intervalIntegral.integral_add_adjacent_intervals (hχi s₁ (s₁ + τ)) (hχi _ s₂),
      ← intervalIntegral.integral_add_adjacent_intervals (hχi (s₁ + τ) (s₂ - τ)) (hχi _ s₂)]
    have e1 : 0 ≤ ∫ t in s₁..s₁ + τ, χ t := intervalIntegral.integral_nonneg hs1 (fun u _ => hχ0 u)
    have e3 : 0 ≤ ∫ t in s₂ - τ..s₂, χ t := intervalIntegral.integral_nonneg hs3 (fun u _ => hχ0 u)
    have e2 : ∫ t in s₁ + τ..s₂ - τ, χ t = s₂ - s₁ - 2 * τ := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
      · simp; ring
      · intro u hu
        rw [uIcc_of_le hs2] at hu
        exact hχmid u hu.1 hu.2
    linarith
  have hIgt : m / σ < I := by
    have : m / σ < s₂ - s₁ - 2 * τ := by rw [hτdef]; linarith
    linarith
  have hIpos : 0 < I := lt_trans (div_pos hm hσ) hIgt
  set σ' : ℝ := m / I with hσ'def
  have hσ'pos : 0 < σ' := div_pos hm hIpos
  have hσ'lt : σ' < σ := by
    rw [hσ'def, div_lt_iff₀ hIpos]
    rw [div_lt_iff₀ hσ] at hIgt
    linarith
  obtain ⟨hFc, hFd⟩ := primitive_contDiff χ hχc s₁
  refine ⟨fun s => σ' * ∫ t in s₁..s, χ t, contDiff_const.mul hFc, ?_⟩
  have hd : ∀ s, deriv (fun s => σ' * ∫ t in s₁..s, χ t) s = σ' * χ s := fun s =>
    ((hFd s).const_mul σ').deriv
  have hlo : ∀ s, s ≤ s₁ → ∫ t in s₁..s, χ t = 0 := by
    intro s hs
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro u hu
      rw [uIcc_of_ge hs] at hu
      exact hχlo u hu.2
  have hhi : ∀ s, s₂ ≤ s → ∫ t in s₁..s, χ t = I := by
    intro s hs
    rw [← intervalIntegral.integral_add_adjacent_intervals (hχi s₁ s₂) (hχi s₂ s)]
    rw [intervalIntegral.integral_congr (a := s₂) (g := fun _ => (0 : ℝ))]
    · simp [hIdef]
    · intro u hu
      rw [uIcc_of_le hs] at hu
      exact hχhi u hu.1
  refine ⟨fun s => by rw [hd]; exact mul_nonneg hσ'pos.le (hχ0 s), fun s => ?_,
    fun s hs => by simp only [hlo s hs, mul_zero], fun s hs => ?_, fun s hs => ?_,
    fun s hs => by rw [hd, hχlo s hs, mul_zero], fun s hs => by rw [hd, hχhi s hs, mul_zero]⟩
  · rw [hd]
    calc σ' * χ s ≤ σ' * 1 := mul_le_mul_of_nonneg_left (hχ1 s) hσ'pos.le
      _ < σ := by linarith
  · simp only [hhi s hs, hσ'def]
    field_simp
  · rcases le_or_gt s s₁ with h1 | h1
    · simp only [hlo s h1, mul_zero]; exact hm
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals (hχi s₁ s) (hχi s s₂)
      have hp : 0 < ∫ t in s..s₂, χ t :=
        intervalIntegral.intervalIntegral_pos_of_pos_on (hχi s s₂)
          (fun u hu => hχpos u (by linarith [hu.1]) hu.2) hs
      have hlt : ∫ t in s₁..s, χ t < I := by rw [hIdef, ← hsplit]; linarith
      have : σ' * I = m := by rw [hσ'def]; field_simp
      show σ' * ∫ t in s₁..s, χ t < m
      rw [← this]
      exact mul_lt_mul_of_pos_left hlt hσ'pos

end Viterbo.Cap.PartA2
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part A2: one-variable profiles -/
alias exists_profile := Viterbo.Cap.PartA2.exists_profile

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
namespace Viterbo.Cap.PartA2
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-- A smooth convex ramp: `0` below `s₀`, slope in `[0, α]`, `ψ(s) ≥ α (s - s₀ - δ)`, and
`ψ'(s) s - ψ(s) ≤ α (s₀ + δ)` for `s ≥ 0`. -/
theorem exists_ramp {s₀ δ α : ℝ} (hs₀ : 0 < s₀) (hδ : 0 < δ) (hα : 0 < α) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ s, s ≤ s₀ → ψ s = 0) ∧ (∀ s, 0 ≤ ψ s) ∧
      (∀ s, 0 ≤ deriv ψ s ∧ deriv ψ s ≤ α) ∧ (∀ s, s₀ + δ ≤ s → deriv ψ s = α) ∧
      (∀ s, α * (s - s₀ - δ) ≤ ψ s) ∧ (∀ s, 0 ≤ s → deriv ψ s * s - ψ s ≤ α * (s₀ + δ)) := by
  set T : ℝ → ℝ := fun u => Real.smoothTransition ((u - s₀) / δ) with hTdef
  have hTc : ContDiff ℝ ∞ T :=
    smoothTransition_contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hTi : ∀ a b, IntervalIntegrable T volume a b := fun a b =>
    hTc.continuous.intervalIntegrable a b
  have hT0 : ∀ u, 0 ≤ T u := fun u => Real.smoothTransition.nonneg _
  have hT1 : ∀ u, T u ≤ 1 := fun u => Real.smoothTransition.le_one _
  have hTlo : ∀ u, u ≤ s₀ → T u = 0 := fun u hu =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  have hThi : ∀ u, s₀ + δ ≤ u → T u = 1 := fun u hu =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδ]; linarith)
  obtain ⟨hFc, hFd⟩ := primitive_contDiff T hTc s₀
  set ψ : ℝ → ℝ := fun s => α * ∫ t in s₀..s, T t with hψdef
  have hd : ∀ s, deriv ψ s = α * T s := fun s => ((hFd s).const_mul α).deriv
  have hlo : ∀ s, s ≤ s₀ → ψ s = 0 := by
    intro s hs
    simp only [hψdef]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro u hu
      rw [uIcc_of_ge hs] at hu
      exact hTlo u hu.2
  have hnn : ∀ s, 0 ≤ ψ s := by
    intro s
    rcases le_total s s₀ with h | h
    · rw [hlo s h]
    · exact mul_nonneg hα.le (intervalIntegral.integral_nonneg h (fun u _ => hT0 u))
  have hlin : ∀ s, α * (s - s₀ - δ) ≤ ψ s := by
    intro s
    rcases le_total s (s₀ + δ) with h | h
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hα.le (by linarith)) (hnn s)
    · simp only [hψdef]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hTi s₀ (s₀ + δ)) (hTi _ s)]
      have e1 : 0 ≤ ∫ t in s₀..s₀ + δ, T t :=
        intervalIntegral.integral_nonneg (by linarith) (fun u _ => hT0 u)
      have e2 : ∫ t in s₀ + δ..s, T t = s - s₀ - δ := by
        rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
        · simp; ring
        · intro u hu
          rw [uIcc_of_le h] at hu
          exact hThi u hu.1
      rw [e2]
      nlinarith
  refine ⟨ψ, contDiff_const.mul hFc, hlo, hnn, fun s => ?_, fun s hs => ?_, hlin, fun s hs => ?_⟩
  · rw [hd]
    exact ⟨mul_nonneg hα.le (hT0 s), by nlinarith [hT1 s, hT0 s]⟩
  · rw [hd, hThi s hs, mul_one]
  · rcases le_total s (s₀ + δ) with h | h
    · rw [hd]
      have h1 : α * T s * s ≤ α * s := by
        nlinarith [mul_nonneg (mul_nonneg hα.le hs) (sub_nonneg.2 (hT1 s))]
      nlinarith [hnn s]
    · rw [hd, hThi s h, mul_one]
      nlinarith [hlin s]

end Viterbo.Cap.PartA2
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
alias exists_ramp := Viterbo.Cap.PartA2.exists_ramp

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartA3
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-!
# Part A3: monotonicity of `c_EHZ` under symplectic embeddings of convex domains

Hofer–Zehnder argument, assembled from the Blueprint stubs.
-/
theorem gradient_eq_zero_of_eventuallyEq [CompleteSpace E] {f : E → ℝ} {x : E} {c : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => c) : gradient f x = 0 := by
  rw [h.gradient_eq]; exact gradient_fun_const x c

theorem hasGradientAt_add' [CompleteSpace E] {f g : E → ℝ} {x f' g' : E} (hf : HasGradientAt f f' x)
    (hg : HasGradientAt g g' x) : HasGradientAt (fun z => f z + g z) (f' + g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_add]; exact hf.add hg

theorem hasGradientAt_comp' [CompleteSpace E] {ψ : ℝ → ℝ} {q : E → ℝ} {x q' : E} {d : ℝ}
    (hψ : HasDerivAt ψ d (q x)) (hq : HasGradientAt q q' x) :
    HasGradientAt (fun z => ψ (q z)) (d • q') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  have h := hψ.comp_hasFDerivAt x hq
  have h2 : (InnerProductSpace.toDual ℝ E) (d • q') = d • (InnerProductSpace.toDual ℝ E) q' := by
    ext v; simp
  rw [h2]; exact h

theorem div_le_gauge {L : Set E} {R : ℝ} (hR : 0 < R) (hL0 : L ∈ 𝓝 (0 : E))
    (hLR : L ⊆ Metric.ball 0 R) (z : E) : ‖z‖ / R ≤ gauge L z := by
  rw [← gauge_ball hR.le]; exact gauge_mono (absorbent_nhds_zero hL0) hLR z

/-- For a convex `L` with `0` in its interior, `{gauge L < 1} ⊆ interior L`. -/
theorem mem_interior_of_gauge_lt_one {L : Set E} (hc : Convex ℝ L) (hL0 : L ∈ 𝓝 (0 : E))
    {z : E} (hz : gauge L z < 1) : z ∈ interior L := by
  have hsub : {w | gauge L w < 1} ⊆ L :=
    setOfPred_gauge_lt_one_subset_self hc (mem_of_mem_nhds hL0) (absorbent_nhds_zero hL0)
  have hopen : IsOpen {w | gauge L w < 1} := isOpen_lt (continuous_gauge hc hL0) continuous_const
  exact interior_maximal hsub hopen hz

end Viterbo.Cap.PartA3
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartA3
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-- The numerical constants of the construction. -/
theorem constants {α A θ₀ : ℝ} (hα : 0 < α) (hαA : α < A) (hθ0 : 0 ≤ θ₀) (hθ1 : θ₀ < 1) :
    ∃ τ s₀ δ s₁ s₂ εK σ m : ℝ, θ₀ < τ ∧ τ < 1 ∧ s₀ = τ ^ 2 ∧ 0 < δ ∧ 0 < s₁ ∧ s₁ < s₂ ∧
      s₂ < 1 ∧ 0 < εK ∧ εK < 1 ∧ εK ^ 2 < s₁ ∧ (2 * εK) ^ 2 ≤ s₁ ∧ 0 < σ ∧ 0 < m ∧
      α * (s₀ + δ) < m ∧ m < σ * (s₂ - s₁) ∧
      ∀ s, s₁ ≤ s → σ * s ≤ (Real.sqrt s - εK) ^ 2 * A := by
  have hA : 0 < A := hα.trans hαA
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (1 + θ₀) / 2 := ⟨_, rfl⟩
  have hθτ : θ₀ < τ := by rw [hτ]; linarith
  have hτ1 : τ < 1 := by rw [hτ]; linarith
  have hτ0 : 0 ≤ τ := by linarith
  have hs1 : τ ^ 2 < 1 := by nlinarith
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = 1 - α * τ ^ 2 / A := ⟨_, rfl⟩
  have hgA : α * τ ^ 2 = A * (1 - g) := by rw [hg]; field_simp; ring
  have hατ : α * τ ^ 2 < A := by nlinarith [sq_nonneg τ]
  have hg0 : 0 < g := by nlinarith
  have hg1 : g ≤ 1 := by nlinarith [sq_nonneg τ]
  have key : α * (τ ^ 2 + g / 4) < (1 - g / 8) ^ 2 * A * ((1 - g / 8) - g ^ 2 / 16) := by
    have h1 : α * (g / 4) < A * (g / 4) := by nlinarith
    have h2 : (1 - g / 4) * (1 - 3 * g / 16) ≤ (1 - g / 8) ^ 2 * ((1 - g / 8) - g ^ 2 / 16) := by
      have ha : 1 - g / 4 ≤ (1 - g / 8) ^ 2 := by nlinarith
      have hb : 1 - 3 * g / 16 ≤ (1 - g / 8) - g ^ 2 / 16 := by nlinarith
      exact mul_le_mul ha hb (by nlinarith) (by positivity)
    have h3 : 1 - 3 * g / 4 < (1 - g / 4) * (1 - 3 * g / 16) := by nlinarith
    nlinarith
  have hαpos : 0 < α * (τ ^ 2 + g / 4) := by positivity
  have hg2 : g ^ 2 ≤ 1 := by nlinarith
  have hg2pos : 0 < g ^ 2 := by positivity
  have hσ : 0 < (1 - g / 8) ^ 2 * A := mul_pos (pow_pos (by linarith) 2) hA
  refine ⟨τ, τ ^ 2, g / 4, g ^ 2 / 16, 1 - g / 8, g ^ 2 / 32, (1 - g / 8) ^ 2 * A,
    (α * (τ ^ 2 + g / 4) + (1 - g / 8) ^ 2 * A * ((1 - g / 8) - g ^ 2 / 16)) / 2, hθτ, hτ1, rfl,
    by positivity, by positivity, by nlinarith, by linarith, by positivity, by nlinarith,
    by nlinarith [mul_le_mul_of_nonneg_left hg2 hg2pos.le],
    by nlinarith [mul_le_mul_of_nonneg_left hg2 hg2pos.le], hσ,
    by linarith, by linarith, by linarith, ?_⟩
  intro s hs
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  have hsq : g / 4 ≤ Real.sqrt s := by
    have := Real.sqrt_le_sqrt (show (g / 4) ^ 2 ≤ s by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at this
  have h1 : (1 - g / 8) * Real.sqrt s ≤ Real.sqrt s - g ^ 2 / 32 := by nlinarith
  have h2 : 0 ≤ (1 - g / 8) * Real.sqrt s := mul_nonneg (by linarith) (Real.sqrt_nonneg s)
  have h3 : ((1 - g / 8) * Real.sqrt s) ^ 2 ≤ (Real.sqrt s - g ^ 2 / 32) ^ 2 :=
    pow_le_pow_left₀ h2 h1 2
  have h4 : ((1 - g / 8) * Real.sqrt s) ^ 2 = (1 - g / 8) ^ 2 * s := by
    rw [mul_pow, Real.sq_sqrt hs0]
  calc (1 - g / 8) ^ 2 * A * s = A * ((1 - g / 8) ^ 2 * s) := by ring
    _ ≤ A * (Real.sqrt s - g ^ 2 / 32) ^ 2 := by
        rw [← h4]; exact mul_le_mul_of_nonneg_left h3 hA.le
    _ = (Real.sqrt s - g ^ 2 / 32) ^ 2 * A := by ring

set_option maxHeartbeats 1000000 in
/-- The asymptotic field: `∇H(ρz)/ρ → α ∇q̂(z)`. -/
theorem asym_aux {n : ℕ} {L' : Set (Vector (Fin n))} {r' : ℝ} (φ' : ContDiffBump (0 : Vector (Fin n)))
    (hBL : Body L' r') {R' : ℝ} (hR'pos : 0 < R') (hL'n : L' ∈ 𝓝 (0 : Vector (Fin n)))
    (hR' : L' ⊆ Metric.ball 0 R') {ψ : ℝ → ℝ} {s₀ δ α Cq M₀ : ℝ}
    (hψd : ∀ s, 0 ≤ deriv ψ s ∧ deriv ψ s ≤ α) (hψdα : ∀ s, s₀ + δ ≤ s → deriv ψ s = α)
    (hsd : 0 ≤ s₀ + δ) (hα : 0 < α) (hCq0 : 0 ≤ Cq) (hCq : ∀ z, z ≠ 0 → ‖gradient (homQ L' φ') z‖ ≤ Cq * ‖z‖)
    (hM₀ : 0 ≤ M₀) {H H₀ P : Vector (Fin n) → ℝ}
    (hgH : ∀ z, gradient H z = gradient H₀ z + gradient P z)
    (hgH₀ : ∀ z, ‖gradient H₀ z‖ ≤ M₀) (hgP0 : gradient P 0 = 0)
    (hgP : ∀ z, z ≠ 0 → gradient P z = deriv ψ (homQ L' φ' z) • gradient (homQ L' φ') z) :
    ∀ B ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ρ, r₀ ≤ ρ → ∀ z : Vector (Fin n), ‖z‖ ≤ B →
      ‖ρ⁻¹ • gradient H (ρ • z) -
        (fun z => α • (if z = 0 then 0 else gradient (homQ L' φ') z)) z‖ ≤ ε := by
  intro B ε hε
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = R' ^ 2 * (s₀ + δ) + 1 := ⟨_, rfl⟩
  have hW0 : 0 < W := by rw [hW]; positivity
  have hr₀ : 0 < (M₀ + α * Cq * W + 1) / ε := by positivity
  refine ⟨(M₀ + α * Cq * W + 1) / ε, hr₀, fun ρ hρ z _ => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hr₀ hρ
  have hρε : (M₀ + α * Cq * W) / ρ ≤ ε := by
    rw [div_le_iff₀ hρ0]
    rw [div_le_iff₀ hε] at hρ
    linarith
  simp only
  have hsplit : ρ⁻¹ • gradient H (ρ • z) - α • (if z = 0 then 0 else gradient (homQ L' φ') z) =
      ρ⁻¹ • gradient H₀ (ρ • z) +
        (ρ⁻¹ • gradient P (ρ • z) - α • (if z = 0 then 0 else gradient (homQ L' φ') z)) := by
    rw [hgH, smul_add]; abel
  have hA1 : ‖ρ⁻¹ • gradient H₀ (ρ • z)‖ ≤ M₀ / ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ0, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hgH₀ _) hρ0.le
  have hA2 : ‖ρ⁻¹ • gradient P (ρ • z) - α • (if z = 0 then 0 else gradient (homQ L' φ') z)‖ ≤
      α * Cq * W / ρ := by
    by_cases hz : z = 0
    · simp only [hz, smul_zero, hgP0, if_true, sub_zero, norm_zero]
      positivity
    · have hρz : ρ • z ≠ 0 := smul_ne_zero hρ0.ne' hz
      rw [hgP _ hρz, gradient_homQ_smul φ' hBL hρ0 hz, homQ_smul φ' hBL hρ0.le, if_neg hz]
      rw [smul_comm (deriv ψ _) ρ, inv_smul_smul₀ hρ0.ne', ← sub_smul, norm_smul,
        Real.norm_eq_abs]
      by_cases hbig : s₀ + δ ≤ ρ ^ 2 * homQ L' φ' z
      · rw [hψdα _ hbig, sub_self, abs_zero, zero_mul]; positivity
      · have habs : |deriv ψ (ρ ^ 2 * homQ L' φ' z) - α| ≤ α := by
          have := hψd (ρ ^ 2 * homQ L' φ' z)
          rw [abs_of_nonpos (by linarith)]; linarith
        have hg1 : ‖z‖ ≤ R' * gauge L' z := by
          have := div_le_gauge hR'pos hL'n hR' z
          rwa [div_le_iff₀ hR'pos, mul_comm] at this
        have hg2 := gauge_sq_le_homQ φ' hBL z
        have hgn := gauge_nonneg (s := L') z
        have hx2 : (ρ * ‖z‖) ^ 2 < W - 1 := by
          calc (ρ * ‖z‖) ^ 2 ≤ (ρ * (R' * gauge L' z)) ^ 2 :=
                pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hg1 hρ0.le) 2
            _ = R' ^ 2 * (ρ ^ 2 * gauge L' z ^ 2) := by ring
            _ ≤ R' ^ 2 * (ρ ^ 2 * homQ L' φ' z) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg2 (by positivity))
                  (by positivity)
            _ < R' ^ 2 * (s₀ + δ) := mul_lt_mul_of_pos_left (lt_of_not_ge hbig) (by positivity)
            _ = W - 1 := by rw [hW]; ring
        have hxn : 0 ≤ ρ * ‖z‖ := mul_nonneg hρ0.le (norm_nonneg z)
        have hx : ρ * ‖z‖ ≤ W := by nlinarith
        have hz' : ‖z‖ ≤ W / ρ := by rw [le_div_iff₀ hρ0]; linarith
        calc |deriv ψ (ρ ^ 2 * homQ L' φ' z) - α| * ‖gradient (homQ L' φ') z‖
            ≤ α * (Cq * (W / ρ)) :=
              mul_le_mul habs ((hCq z hz).trans (mul_le_mul_of_nonneg_left hz' hCq0))
                (norm_nonneg _) hα.le
          _ = α * Cq * W / ρ := by ring
  rw [hsplit]
  calc ‖ρ⁻¹ • gradient H₀ (ρ • z) +
        (ρ⁻¹ • gradient P (ρ • z) - α • (if z = 0 then 0 else gradient (homQ L' φ') z))‖
      ≤ ‖ρ⁻¹ • gradient H₀ (ρ • z)‖ +
        ‖ρ⁻¹ • gradient P (ρ • z) - α • (if z = 0 then 0 else gradient (homQ L' φ') z)‖ :=
          norm_add_le _ _
    _ ≤ M₀ / ρ + α * Cq * W / ρ := add_le_add hA1 hA2
    _ = (M₀ + α * Cq * W) / ρ := by ring
    _ ≤ ε := hρε

set_option maxHeartbeats 1000000 in
/-- The assembly, after the bridge and the trigonometric loop. -/
theorem core {n : ℕ} (hn : 1 ≤ n) {K' L' : Set (Vector (Fin n))} {r : ℝ}
    (e : OpenPartialHomeomorph (Vector (Fin n)) (Vector (Fin n)))
    (hK : Body K' r) (hKd : IsConvexDomain (Capacities.Ψ n '' K'))
    {A α : ℝ} (hA : (cEHZ (Capacities.Ψ n '' K')).toReal = A) (hα : 0 < α) (hαA : α < A)
    (hL'c : Convex ℝ L') (hL'b : Bornology.IsBounded L')
    (hL'0 : (0 : Vector (Fin n)) ∈ interior L')
    (hsrc : e.source = interior K') (h0 : (0 : Vector (Fin n)) ∈ e.source) (he0 : e 0 = 0)
    (hes : ContDiffOn ℝ ∞ e e.source)
    (hω : ∀ w ∈ e.source, OAI.ComplexSymplectic.Preserves (fderiv ℝ e w))
    {θ : ℝ} (hθ : θ < 1) (hθe : ∀ w ∈ e.source, gauge L' (e w) ≤ θ)
    {D : ℕ} {b : ℤ → Vector (Fin n)}
    (hW : ∫ t in (0 : ℝ)..1, supportFn L' (-(Complex.I • trigVel D b t)) ^ 2 <
      4 * α * trigAction D b) : False := by
  have hApos : 0 < A := hα.trans hαA
  have hL'n : L' ∈ 𝓝 (0 : Vector (Fin n)) := mem_interior_iff_mem_nhds.mp hL'0
  have hK'n : K' ∈ 𝓝 (0 : Vector (Fin n)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hK.rpos) hK.ball
  obtain ⟨r', hr', hball'⟩ := Metric.mem_nhds_iff.mp hL'n
  have hBL : Body L' r' := ⟨hL'c, hL'b, hr', hball'⟩
  obtain ⟨R', hR'⟩ := hL'b.subset_ball (0 : Vector (Fin n))
  have hR'pos : 0 < R' := by simpa using hR' (mem_of_mem_nhds hL'n)
  have heL : ∀ w ∈ e.source, ‖e w‖ < R' := by
    intro w hw
    have h1 : e w ∈ L' := setOfPred_gauge_lt_one_subset_self hL'c (mem_of_mem_nhds hL'n)
      (absorbent_nhds_zero hL'n) ((hθe w hw).trans_lt hθ)
    simpa using hR' h1
  have h0t : (0 : Vector (Fin n)) ∈ e.target := by simpa [he0] using e.map_source h0
  obtain ⟨τ, s₀, δ, s₁, s₂, εK, σ, m, hθτ, hτ1, hs₀τ, hδ, hs₁, hs₁₂, hs₂1, hεK, hεK1, hεKs₁,
    h2εK, hσ, hm0, hm1, hm2, hslowc⟩ := constants hα hαA (le_max_right θ 0) (max_lt hθ one_pos)
  have hτ0 : 0 < τ := (le_max_right θ 0).trans_lt hθτ
  have hs₀ : 0 < s₀ := by rw [hs₀τ]; positivity
  have hτθ : 0 < τ - max θ 0 := sub_pos.mpr hθτ
  have hrO' : 0 < (τ - max θ 0) * r' / R' := div_pos (mul_pos hτθ hr') hR'pos
  have hrO : 0 < εK * r := mul_pos hεK hK.rpos
  let φ' : ContDiffBump (0 : Vector (Fin n)) :=
    ⟨(τ - max θ 0) * r' / R' / 2, (τ - max θ 0) * r' / R', div_pos hrO' two_pos,
      half_lt_self hrO'⟩
  let φ : ContDiffBump (0 : Vector (Fin n)) :=
    ⟨εK * r / 2, εK * r, div_pos hrO two_pos, half_lt_self hrO⟩
  have hφr : φ.rOut / r = εK := mul_div_cancel_right₀ _ hK.rpos.ne'
  have hφ : φ.rOut < r := mul_lt_of_lt_one_left hK.rpos hεK1
  obtain ⟨f, hfs, hf0, hfσ, hflow, hfhigh, hflt, hdlow, hdhigh⟩ := exists_profile hs₁₂ hσ hm0 hm2
  obtain ⟨ψ, hψs, hψ0, hψnn, hψd, hψdα, hψlow, hψG⟩ := exists_ramp hs₀ hδ hα
  have hQs : ContDiff ℝ ∞ (mollQ K' φ) := contDiff_mollQ φ hK
  have hfle : ∀ s, f s ≤ m := by
    intro s
    by_cases h : s₂ ≤ s
    · exact (hfhigh s h).le
    · exact (hflt s (lt_of_not_ge h)).le
  have hfnn : ∀ s, 0 ≤ f s := by
    intro s
    have hmono : Monotone f := monotone_of_deriv_nonneg (hfs.differentiable (by simp)) hf0
    by_cases h : s ≤ s₁
    · exact (hflow s h).ge
    · rw [← hflow s₁ le_rfl]; exact hmono (le_of_not_ge h)
  have hq_src : ∀ w ∈ e.source, homQ L' φ' (e w) ≤ s₀ := by
    intro w hw
    have h1 := homQ_le φ' hBL (e w)
    have hg := (hθe w hw).trans (le_max_left θ 0)
    have hgn := gauge_nonneg (s := L') (e w)
    have hn := heL w hw
    have h2 : φ'.rOut * ‖e w‖ / r' ≤ τ - max θ 0 := by
      show (τ - max θ 0) * r' / R' * ‖e w‖ / r' ≤ τ - max θ 0
      rw [div_le_iff₀ hr']
      have : (τ - max θ 0) * r' / R' * ‖e w‖ ≤ (τ - max θ 0) * r' := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hR'pos]
        exact mul_le_mul_of_nonneg_left hn.le (mul_pos hτθ hr').le
      linarith
    have h3 : 0 ≤ φ'.rOut * ‖e w‖ / r' := div_nonneg (mul_nonneg hrO'.le (norm_nonneg _)) hr'.le
    rw [hs₀τ]
    exact h1.trans (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have hq_nn : ∀ z, 0 ≤ homQ L' φ' z := fun z => (sq_nonneg _).trans (gauge_sq_le_homQ φ' hBL z)
  set S : Set (Vector (Fin n)) := {w | mollQ K' φ w ≤ s₂} with hSdef
  have hSsrc : S ⊆ e.source := by
    intro w hwS
    have h1 := gauge_sq_le_mollQ φ hK w
    have hwS' : mollQ K' φ w ≤ s₂ := hwS
    have h2 : gauge K' w < 1 := by
      by_contra h
      push Not at h
      nlinarith
    rw [hsrc]; exact mem_interior_of_gauge_lt_one hK.convex hK'n h2
  have hScpt : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_le hQs.continuous continuous_const)
      (hK.bounded.subset (fun w hw => interior_subset (hsrc ▸ hSsrc hw)))
  have hQ0 : mollQ K' φ 0 < s₁ := by
    have := mollQ_le φ hK 0
    rw [gauge_zero, zero_add, hφr] at this
    linarith
  have h0S : (0 : Vector (Fin n)) ∈ S := by
    show mollQ K' φ 0 ≤ s₂; linarith
  set F : Vector (Fin n) → ℝ := fun w => f (mollQ K' φ w) - m with hFdef
  have hFs : ContDiff ℝ ∞ F := (hfs.comp hQs).sub contDiff_const
  have hFz : ∀ w ∉ S, F w = 0 := by
    intro w hw
    have : s₂ < mollQ K' φ w := lt_of_not_ge hw
    show f (mollQ K' φ w) - m = 0
    rw [hfhigh _ this.le, sub_self]
  have hD : ∀ w ∈ e.source, (fderiv ℝ e w).IsInvertible :=
    fun w hw => ComplexSymplectic.invertible (hω w hw)
  set H₀ : Vector (Fin n) → ℝ := fun z => EmbeddingInverse.extendFunction e F z + m with hH₀def
  set P : Vector (Fin n) → ℝ := fun z => ψ (homQ L' φ' z) with hPdef
  set H : Vector (Fin n) → ℝ := fun z => H₀ z + P z with hHdef
  have hH₀s : ContDiff ℝ ∞ H₀ :=
    (EmbeddingInverse.contDiff_extendFunction e hes hD hFs hScpt hSsrc hFz).add contDiff_const
  have hPtgt : ∀ z ∈ e.target, P z = 0 := by
    intro z hz
    have := hq_src _ (e.map_target hz)
    rw [e.right_inv hz] at this
    exact hψ0 _ this
  have hPev : P =ᶠ[𝓝 (0 : Vector (Fin n))] fun _ => (0 : ℝ) := by
    filter_upwards [e.open_target.mem_nhds h0t] with y hy
    exact hPtgt y hy
  have hPs : ContDiff ℝ ∞ P := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      exact contDiffAt_const.congr_of_eventuallyEq hPev
    · exact hψs.contDiffAt.comp z (contDiffAt_homQ φ' hBL hz)
  have hHs : ContDiff ℝ ∞ H := hH₀s.add hPs
  set T := e '' S with hTdef
  have hTcpt : IsCompact T := hScpt.image_of_continuousOn (e.continuousOn.mono hSsrc)
  have h0T : (0 : Vector (Fin n)) ∈ T := ⟨0, h0S, he0⟩
  have hH₀off : ∀ z ∉ T, H₀ z = m := by
    intro z hz
    show EmbeddingInverse.extendFunction e F z + m = m
    rw [EmbeddingInverse.extendFunction_zero e F S hFz hz, zero_add]
  have hgH₀off : ∀ z ∉ T, gradient H₀ z = 0 := by
    intro z hz
    apply gradient_eq_zero_of_eventuallyEq (c := m)
    filter_upwards [hTcpt.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact hH₀off y hy
  obtain ⟨M₀, hM₀, hgH₀⟩ : ∃ M₀, 0 ≤ M₀ ∧ ∀ z, ‖gradient H₀ z‖ ≤ M₀ := by
    have hcont : Continuous (gradient H₀) := by
      show Continuous fun z => (InnerProductSpace.toDual ℝ (Vector (Fin n))).symm (fderiv ℝ H₀ z)
      exact (InnerProductSpace.toDual ℝ (Vector (Fin n))).symm.continuous.comp
        (hH₀s.continuous_fderiv (by simp))
    obtain ⟨M, hM⟩ := hTcpt.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun z => ?_⟩
    by_cases hz : z ∈ T
    · exact (hM z hz).trans (le_max_left _ _)
    · rw [hgH₀off z hz, norm_zero]; exact le_max_right _ _
  have hcomp : ∀ w ∈ e.source, H (e w) = f (mollQ K' φ w) := by
    intro w hw
    show EmbeddingInverse.extendFunction e F (e w) + m + ψ (homQ L' φ' (e w)) = f (mollQ K' φ w)
    rw [EmbeddingInverse.extendFunction_apply e F hw, hψ0 _ (hq_src w hw)]
    simp only [hFdef]; ring
  have hgP0 : gradient P 0 = 0 := gradient_eq_zero_of_eventuallyEq hPev
  have hgP : ∀ z, z ≠ 0 → gradient P z = deriv ψ (homQ L' φ' z) • gradient (homQ L' φ') z := by
    intro z hz
    exact (hasGradientAt_comp' ((hψs.differentiable (by simp)) _).hasDerivAt
      ((contDiffAt_homQ φ' hBL hz).differentiableAt (by simp)).hasGradientAt).gradient
  have hgH : ∀ z, gradient H z = gradient H₀ z + gradient P z := by
    intro z
    exact (hasGradientAt_add' ((hH₀s.differentiable (by simp)) z).hasGradientAt
      ((hPs.differentiable (by simp)) z).hasGradientAt).gradient
  obtain ⟨Cq, hCq0, hCq⟩ := norm_gradient_homQ_le φ' hBL
  set γ₀ := m - α * (s₀ + δ) with hγ₀def
  have hγ₀ : 0 < γ₀ := sub_pos.mpr hm1
  have hGoff : ∀ z ∉ T, inner (𝕜 := ℝ) (gradient H z) z / 2 - H z ≤ -γ₀ := by
    intro z hz
    have hz0 : z ≠ 0 := fun h => hz (h ▸ h0T)
    have hHz : H z = m + ψ (homQ L' φ' z) := by
      show H₀ z + P z = _
      rw [hH₀off z hz]
    rw [hgH, hgH₀off z hz, hgP z hz0, zero_add, real_inner_smul_left,
      inner_gradient_homQ φ' hBL hz0, hHz]
    have := hψG (homQ L' φ' z) (hq_nn z)
    have h2 : deriv ψ (homQ L' φ' z) * (2 * homQ L' φ' z) / 2 =
        deriv ψ (homQ L' φ' z) * homQ L' φ' z := by ring
    rw [h2, hγ₀def]
    linarith
  have hH₀nn : ∀ z, 0 ≤ H₀ z := by
    intro z
    show 0 ≤ EmbeddingInverse.extendFunction e F z + m
    rcases EmbeddingInverse.extendFunction_mem_range e F z with h | ⟨v, -, h⟩
    · rw [h]; linarith
    · rw [h]; simp only [hFdef]; linarith [hfnn (mollQ K' φ v)]
  have hH0 : ∀ z, 0 ≤ H z := fun z => add_nonneg (hH₀nn z) (hψnn _)
  have hHoff : ∀ z ∉ T, m ≤ H z := by
    intro z hz
    show m ≤ H₀ z + P z
    rw [hH₀off z hz]; linarith [hψnn (homQ L' φ' z)]
  set V : Vector (Fin n) → Vector (Fin n) :=
    fun z => α • (if z = 0 then 0 else gradient (homQ L' φ') z) with hVdef
  obtain ⟨RT, hRT⟩ := hTcpt.isBounded.subset_ball (0 : Vector (Fin n))
  have hEng : EngineHyp H V (max M₀ (α * Cq)) RT γ₀ := by
    refine ⟨hHs, ?_, ?_, ?_, ?_, hγ₀, ?_⟩
    · -- grow
      intro z
      rw [hgH]
      have h1 : ‖gradient P z‖ ≤ α * Cq * ‖z‖ := by
        by_cases hz : z = 0
        · rw [hz, hgP0, norm_zero, mul_zero]
        · rw [hgP z hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψd _).1]
          calc deriv ψ (homQ L' φ' z) * ‖gradient (homQ L' φ') z‖ ≤ α * (Cq * ‖z‖) :=
                mul_le_mul (hψd _).2 (hCq z hz) (norm_nonneg _) hα.le
            _ = α * Cq * ‖z‖ := by ring
      have hm1 := le_max_left M₀ (α * Cq)
      have hm2 := le_max_right M₀ (α * Cq)
      calc ‖gradient H₀ z + gradient P z‖ ≤ ‖gradient H₀ z‖ + ‖gradient P z‖ := norm_add_le _ _
        _ ≤ M₀ + α * Cq * ‖z‖ := add_le_add (hgH₀ z) h1
        _ ≤ max M₀ (α * Cq) * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
    · -- contV
      exact (continuous_gradient_homQ φ' hBL).const_smul α
    · -- linV
      intro z
      by_cases hz : z = 0
      · simp only [hVdef, hz, if_true, smul_zero, norm_zero, mul_zero, le_refl]
      · simp only [hVdef, if_neg hz, norm_smul, Real.norm_eq_abs, abs_of_pos hα]
        calc α * ‖gradient (homQ L' φ') z‖ ≤ α * (Cq * ‖z‖) :=
              mul_le_mul_of_nonneg_left (hCq z hz) hα.le
          _ = (α * Cq) * ‖z‖ := by ring
          _ ≤ max M₀ (α * Cq) * ‖z‖ :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    · -- asym
      exact asym_aux φ' hBL hR'pos hL'n hR' hψd hψdα (add_pos hs₀ hδ).le hα hCq0 hCq hM₀ hgH hgH₀ hgP0 hgP
    · -- outer
      intro z hz
      apply hGoff
      intro hzT
      have := hRT hzT
      rw [Metric.mem_ball, dist_zero_right] at this
      linarith
  have hflat : ∀ᶠ z in 𝓝 (0 : Vector (Fin n)), H z = 0 := by
    have hev : ∀ᶠ w in 𝓝 (0 : Vector (Fin n)), H (e w) = 0 := by
      filter_upwards [e.open_source.mem_nhds h0,
        (isOpen_lt hQs.continuous continuous_const).mem_nhds hQ0] with w hw hwQ
      rw [hcomp w hw]
      exact hflow _ (le_of_lt hwQ)
    have := EmbeddingInverse.eventually_of_comp e h0 (P := fun z => H z = 0) hev
    rwa [he0] at this
  have hcone : ConeHyp H := by
    refine coneHyp_of_lower hHs.continuous hL'c hL'b hL'0 hα (C₀ := α * (s₀ + δ)) ?_ hW
    intro z
    have h1 := hψlow (homQ L' φ' z)
    have h2 := gauge_sq_le_homQ φ' hBL z
    have h3 : α * gauge L' z ^ 2 ≤ α * homQ L' φ' z := mul_le_mul_of_nonneg_left h2 hα.le
    have h4 := hH₀nn z
    show _ ≤ H₀ z + ψ (homQ L' φ' z)
    nlinarith
  obtain ⟨x, hx1, hxpos, hx⟩ := engine hEng hH0 hflat hcone
  -- the orbit
  have hexists : ∃ t, 0 < inner (𝕜 := ℝ) (gradient H (x t)) (x t) / 2 - H (x t) := by
    by_contra hno
    push Not at hno
    have h1 := intervalIntegral.integral_nonneg_of_forall (μ := volume) zero_le_one
      (fun s => neg_nonneg.mpr (hno s))
    rw [intervalIntegral.integral_neg] at h1
    unfold actionIntegral at hxpos
    linarith
  obtain ⟨t, ht⟩ := hexists
  have hxT : x t ∈ T := by
    by_contra h
    have := hGoff _ h
    linarith
  obtain ⟨w, hwS, hwx⟩ := hxT
  have hw : w ∈ e.source := hSsrc hwS
  have hGs : ContDiff ℝ ∞ (fun w => f (mollQ K' φ w)) := hfs.comp hQs
  have hlev : H (x t) < m := by
    have hHx : H (x t) = f (mollQ K' φ w) := by rw [← hwx]; exact hcomp w hw
    rcases (hfle (mollQ K' φ w)).lt_or_eq with h | h
    · rwa [hHx]
    exfalso
    have hQw : s₂ ≤ mollQ K' φ w := by
      by_contra hc
      push Not at hc
      exact (hflt _ hc).ne h
    have hgG : gradient (fun w => f (mollQ K' φ w)) w = 0 := by
      rw [(hasGradientAt_comp' ((hfs.differentiable (by simp)) _).hasDerivAt
        ((hQs.differentiable (by simp)) w).hasGradientAt).gradient, hdhigh _ hQw, zero_smul]
    have hpush := ComplexSymplectic.push_hamiltonian e hes hω hHs hGs hcomp hw
    rw [hgG, smul_zero, map_zero, hwx] at hpush
    have hgx : gradient H (x t) = 0 := by
      have := hpush.symm
      rwa [smul_eq_zero, or_iff_right Complex.I_ne_zero] at this
    rw [hgx, inner_zero_left, hHx, h] at ht
    linarith
  have hall : ∀ s, x s ∈ e.target := by
    intro s
    have hEs := OAI.HamiltonianODE.energy_constant hHs hx s t
    by_contra hs
    have hxs : x s ∉ T := by
      rintro ⟨v, hv, hvx⟩
      exact hs (hvx ▸ e.map_source (hSsrc hv))
    have := hHoff _ hxs
    linarith
  have hy := ComplexSymplectic.inverse_curve e hes hω hHs hGs hcomp hall hx
  have hfa : ∀ s, s ≤ (2 * φ.rOut / r) ^ 2 → deriv f s = 0 := by
    intro s hs
    apply hdlow
    rw [mul_div_assoc, hφr] at hs
    linarith
  have hslow : ∀ s, 0 < deriv f s →
      deriv f s * s < (Real.sqrt s - φ.rOut / r) ^ 2 * (cEHZ (Capacities.Ψ n '' K')).toReal := by
    intro s hs
    rw [hφr, hA]
    have hs1 : s₁ < s := by
      by_contra h
      push Not at h
      rw [hdlow s h] at hs
      exact lt_irrefl _ hs
    calc deriv f s * s < σ * s := mul_lt_mul_of_pos_right (hfσ s) (by linarith)
      _ ≤ _ := hslowc s hs1.le
  have hconst := orbit_const_of_slow hn hK hKd φ hφ hfs hf0 hfa hslow hy (by simp [hx1])
  have hxc : ∀ s, x s = x 0 := fun s => by
    have := congrArg e (hconst s)
    rwa [e.right_inv (hall s), e.right_inv (hall 0)] at this
  have hgrad0 : gradient H (x t) = 0 := by
    have hxfun : x = fun _ => x 0 := funext hxc
    have h1 : HasDerivAt x 0 t := by
      rw [hxfun]; exact hasDerivAt_const t (x 0)
    have h2 := (hx t).unique h1
    rwa [smul_eq_zero, or_iff_right Complex.I_ne_zero] at h2
  rw [hgrad0, inner_zero_left] at ht
  linarith [hH0 (x t)]

theorem cEHZ_le_of_hse {n : ℕ} (hn : 1 ≤ n) {K L : Set (Phase n)} (hK : IsConvexDomain K)
    (hL : IsConvexDomain L) (he : HasSymplecticEmbedding K L) : cEHZ K ≤ cEHZ L := by
  by_contra hlt
  push Not at hlt
  obtain ⟨γK, -, -, hAK, hcK, -⟩ := Viterbo.CM.exists_char_cEHZ_eq hn hK
  obtain ⟨γL, -, -, hAL, hcL, -⟩ := Viterbo.CM.exists_char_cEHZ_eq hn hL
  set AK := Viterbo.action γK with hAKdef
  set AL := Viterbo.action γL with hALdef
  rw [hcK, hcL, ENNReal.ofReal_lt_ofReal_iff hAK] at hlt
  set η := Real.sqrt ((AL + AK) / (2 * AL)) - 1 with hηdef
  have hq1 : 1 < (AL + AK) / (2 * AL) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hη2 : (1 + η) ^ 2 = (AL + AK) / (2 * AL) := by
    rw [hηdef, add_sub_cancel, Real.sq_sqrt (by linarith)]
  have hη : 0 < η := by
    rw [hηdef, sub_pos, Real.lt_sqrt (by norm_num)]; linarith
  obtain ⟨K', L', r, e, hKb, hKd, hKc, hLd, hL0, hLc, hsrc, h0, he0, hes, hω, θ, hθ, hθe⟩ :=
    bridge hn hK hL he hη
  set α := (AL + 3 * AK) / 4 with hαdef
  have hcL' : cEHZ (Capacities.Ψ n '' L') < ENNReal.ofReal α := by
    rw [hLc, hcL, ← ENNReal.ofReal_mul (by positivity), hη2,
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hAL.ne']
    linarith
  obtain ⟨D, b, hW⟩ := exists_trig_loop hn hLd hL0 hcL'
  have hΦΨ : Capacities.Φ n '' (Capacities.Ψ n '' L') = L' := by
    rw [Set.image_image]; simp [Capacities.Φ_Ψ]
  rw [hΦΨ] at hW
  have hL'c : Convex ℝ L' := by
    have := hLd.2.1.linear_image (Capacities.Φ n).toLinearMap
    rwa [ContinuousLinearMap.coe_coe, hΦΨ] at this
  have hL'b : Bornology.IsBounded L' := by
    have := (Capacities.Φ n).lipschitz.isBounded_image hLd.1
    rwa [hΦΨ] at this
  have hL'0 : (0 : Vector (Fin n)) ∈ interior L' := by
    rw [mem_interior]
    refine ⟨Capacities.Ψ n ⁻¹' interior (Capacities.Ψ n '' L'), ?_,
      isOpen_interior.preimage (Capacities.Ψ n).continuous, by simpa using hL0⟩
    intro w hw
    obtain ⟨v, hv, hvw⟩ := interior_subset hw
    have := congrArg (Capacities.Φ n) hvw
    rw [Capacities.Φ_Ψ, Capacities.Φ_Ψ] at this
    rwa [← this]
  have hA : (cEHZ (Capacities.Ψ n '' K')).toReal = AK := by
    rw [hKc, hcK, ENNReal.toReal_ofReal hAK.le]
  exact core hn e hKb hKd hA (by positivity) (by linarith) hL'c hL'b hL'0 hsrc h0 he0 hes hω hθ
    hθe hW

end Viterbo.Cap.PartA3
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part A3: monotonicity of `c_EHZ` under symplectic embeddings of convex domains -/

/-! ## Part P: the envelope capacity and the target -/

end Viterbo.Cap
end
end

theorem solution : type_of% @Viterbo.Cap.PartA3.cEHZ_le_of_hse := @Viterbo.Cap.PartA3.cEHZ_le_of_hse
