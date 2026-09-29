-- Prove2me | solution 1 for candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-07-06T00:00:30.998348+00:00
-- url     : https://prove2.me/submissions/b43fcc41-57ad-4afb-b68f-eadc48fec221

/- Solution: Talagrand/Ledoux/Klein-Rio concentration for the supremum of a
finite Boolean-product linear process (Candes-Romberg Theorem 3.2 form).
Upper tail: Ledoux ESAIM 1996 Thm 2.4/2.5 (self-bounding + two-copy entropy +
truncation). Lower tail: Klein-Rio Ann. Probab. 2005 Thm 1.2 (compensated
process, generalized tensorization, frozen-branch Dini integration) plus a
single-branch Bennett bound for the far regime. Everything is developed over
the finite cube via exact weighted sums (`Ex`), then bridged to the
`Measure.pi` Bochner integral. Uses the proved platform brick
`entropy_n_coordinate_han_subadditivity_measure_pi_pos` (Han subadditivity). -/

import Definitions.Def_matrix_completion_bernoulli_measure
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Lattice
import Theorems.Thm_entropy_n_coordinate_han_subadditivity_measure_pi_pos

/-! ## Component: Arith -/
section
/-
Standalone real-analysis lemmas: Bennett/log-form conversions, prefactor
absorption.  No dependencies on the process development.
-/

namespace TalagrandCore

open Real

/-- Helper: a function vanishing at `0` with nonnegative derivative on
`(0,∞)` is nonnegative on `[0,∞)`. -/
theorem nonneg_of_deriv_nonneg_Ici {f f' : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ x → HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, 0 < x → 0 ≤ f' x) :
    ∀ u, 0 ≤ u → 0 ≤ f u := by
  have hmono : MonotoneOn f (Set.Ici (0:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      exact (hf x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact ((hf x (le_of_lt hx)).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hf x (le_of_lt hx)).deriv]
      exact hd x hx
  intro u hu
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  linarith [h0 ▸ this]

/-- Padé bound: `2u/(2+u) ≤ log(1+u)` for `u ≥ 0`. -/
theorem two_mul_div_le_log (u : ℝ) (hu : 0 ≤ u) :
    2 * u / (2 + u) ≤ Real.log (1 + u) := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun x => Real.log (1 + x) - 2 * x / (2 + x))
    (f' := fun x => 1 / (1 + x) - 4 / (2 + x) ^ 2)
    (fun x hx => by
      have h1 : (0:ℝ) < 1 + x := by linarith
      have h2 : (0:ℝ) < 2 + x := by linarith
      have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
        have hin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
        exact hin.log h1.ne'
      have hq : HasDerivAt (fun y : ℝ => 2 * y / (2 + y)) (4 / (2 + x) ^ 2) x := by
        have hnum : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
          simpa using (hasDerivAt_id x).const_mul (2:ℝ)
        have hden : HasDerivAt (fun y : ℝ => 2 + y) 1 x := (hasDerivAt_id x).const_add 2
        have := hnum.div hden h2.ne'
        exact this.congr_deriv (by ring)
      exact hlog.sub hq)
    (by norm_num)
    (fun x hx => by
      have h1 : (0:ℝ) < 1 + x := by linarith
      have h2 : (0:ℝ) < 2 + x := by linarith
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) h1]
      nlinarith [sq_nonneg x])
    u hu
  linarith [key]

/-- Bennett's `h`: `h u = (1+u)·log(1+u) − u`. -/
noncomputable def hBen (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u

/-- `h(u) ≥ (u/2)·log(1+u)` for `u ≥ 0`. -/
theorem hBen_ge_half_mul_log (u : ℝ) (hu : 0 ≤ u) :
    u / 2 * Real.log (1 + u) ≤ hBen u := by
  have hlog := two_mul_div_le_log u hu
  have h2u : (0:ℝ) < 2 + u := by linarith
  unfold hBen
  have hkey : (1 + u / 2) * (2 * u / (2 + u)) = u := by
    field_simp
  nlinarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ 1 + u),
    mul_le_mul_of_nonneg_left hlog (by linarith : (0:ℝ) ≤ 1 + u / 2)]

/-- Denominator absorption: for `c ≥ 1`, `u ≥ 0`:
`log(1 + u/c) ≥ log(1 + u)/c`. -/
theorem log_one_add_div_ge (c u : ℝ) (hc : 1 ≤ c) (hu : 0 ≤ u) :
    Real.log (1 + u) / c ≤ Real.log (1 + u / c) := by
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le one_pos hc
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun x => Real.log (1 + x / c) - Real.log (1 + x) / c)
    (f' := fun x => (1 / c) / (1 + x / c) - (1 / (1 + x)) / c)
    (fun x hx => by
      have h1 : (0:ℝ) < 1 + x := by linarith
      have h1c : (0:ℝ) < 1 + x / c := by positivity
      have hlog1 : HasDerivAt (fun y : ℝ => Real.log (1 + y / c)) ((1 / c) / (1 + x / c)) x := by
        have hin : HasDerivAt (fun y : ℝ => 1 + y / c) (1 / c) x := by
          simpa using ((hasDerivAt_id x).div_const c).const_add 1
        exact hin.log h1c.ne'
      have hlog2 : HasDerivAt (fun y : ℝ => Real.log (1 + y) / c) ((1 / (1 + x)) / c) x := by
        have hin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
        exact (hin.log h1.ne').div_const c
      exact hlog1.sub hlog2)
    (by simp)
    (fun x hx => by
      have h1 : (0:ℝ) < 1 + x := by linarith
      have h1c : (0:ℝ) < 1 + x / c := by positivity
      have hle : 1 + x / c ≤ 1 + x := by
        have : x / c ≤ x := by
          rw [div_le_iff₀ hc0]
          nlinarith
        linarith
      rw [sub_nonneg, div_div, div_div]
      have hc1 : c * (1 + x / c) = c + x := by field_simp
      rw [hc1]
      apply one_div_le_one_div_of_le (by linarith)
      nlinarith)
    u hu
  linarith [key]

/-- Argument scaling: for `0 < s ≤ 1`, `u ≥ 0`:
`log(1 + s·u) ≥ s·log(1 + u)`. -/
theorem log_one_add_mul_ge (s u : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (hu : 0 ≤ u) :
    s * Real.log (1 + u) ≤ Real.log (1 + s * u) := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun x => Real.log (1 + s * x) - s * Real.log (1 + x))
    (f' := fun x => s / (1 + s * x) - s / (1 + x))
    (fun x hx => by
      have h1 : (0:ℝ) < 1 + x := by linarith
      have h1s : (0:ℝ) < 1 + s * x := by nlinarith
      have hlog1 : HasDerivAt (fun y : ℝ => Real.log (1 + s * y)) (s / (1 + s * x)) x := by
        have hin : HasDerivAt (fun y : ℝ => 1 + s * y) s x := by
          simpa using ((hasDerivAt_id x).const_mul s).const_add 1
        exact hin.log h1s.ne'
      have hlog2 : HasDerivAt (fun y : ℝ => s * Real.log (1 + y)) (s / (1 + x)) x := by
        have hin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
        have h := (hin.log h1.ne').const_mul s
        rw [mul_one_div] at h
        exact h
      exact hlog1.sub hlog2)
    (by simp)
    (fun x hx => by
      have h1 : (0:ℝ) < 1 + x := by linarith
      have h1s : (0:ℝ) < 1 + s * x := by nlinarith
      have hle : 1 + s * x ≤ 1 + x := by nlinarith
      rw [sub_nonneg]
      gcongr)
    u hu
  linarith [key]

/-- Prefactor absorption: if `P ≤ 1` and `P ≤ A·e^{−E}` with `A ≥ 3`, `E ≥ 0`,
then `P ≤ 3·e^{−E/K}` for every `K ≥ log A / log 3`, `K ≥ 1`. -/
theorem prefactor_absorb (P A E K : ℝ) (hP1 : P ≤ 1) (hPA : P ≤ A * Real.exp (-E))
    (hA : 3 ≤ A) (hE : 0 ≤ E) (hK1 : 1 ≤ K) (hK : Real.log A / Real.log 3 ≤ K) :
    P ≤ 3 * Real.exp (-(E / K)) := by
  by_cases hcase : E ≤ K * Real.log 3
  · have hKpos : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
    have hexp : Real.exp (-(Real.log 3)) ≤ Real.exp (-(E / K)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, div_le_iff₀ hKpos]
      calc E ≤ K * Real.log 3 := hcase
        _ = Real.log 3 * K := by ring
    have h3 : Real.exp (-(Real.log 3)) = 1 / 3 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 3)]
      norm_num
    rw [h3] at hexp
    calc P ≤ 1 := hP1
      _ ≤ 3 * Real.exp (-(E / K)) := by nlinarith
  · push_neg at hcase
    have hKpos : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
    have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have key : Real.log A - Real.log 3 ≤ E - E / K := by
      have h1 : Real.log A ≤ K * Real.log 3 := by
        rw [div_le_iff₀ hlog3] at hK; linarith
      have hKr : K * (1 / K) = 1 := by field_simp
      have hr1 : 1 / K ≤ 1 := by rw [div_le_one hKpos]; exact hK1
      have hr0 : (0:ℝ) < 1 / K := by positivity
      have hEr : E / K = E * (1 / K) := by rw [div_eq_mul_one_div]
      rw [hEr]
      have hprod : K * Real.log 3 * (1 - 1/K) ≤ E * (1 - 1/K) :=
        mul_le_mul_of_nonneg_right (le_of_lt hcase) (by linarith)
      nlinarith [hprod, hKr, h1, hlog3]
    calc P ≤ A * Real.exp (-E) := hPA
      _ ≤ 3 * Real.exp (-(E / K)) := by
          have hA0 : (0:ℝ) < A := by linarith
          have e1 : A * Real.exp (-E) = Real.exp (Real.log A - E) := by
            calc A * Real.exp (-E)
                = Real.exp (Real.log A) * Real.exp (-E) := by rw [Real.exp_log hA0]
              _ = Real.exp (Real.log A + -E) := (Real.exp_add _ _).symm
              _ = Real.exp (Real.log A - E) := by ring_nf
          have e2 : (3:ℝ) * Real.exp (-(E/K)) = Real.exp (Real.log 3 - E/K) := by
            calc (3:ℝ) * Real.exp (-(E/K))
                = Real.exp (Real.log 3) * Real.exp (-(E/K)) := by
                  rw [Real.exp_log (by norm_num : (0:ℝ) < 3)]
              _ = Real.exp (Real.log 3 + -(E/K)) := (Real.exp_add _ _).symm
              _ = Real.exp (Real.log 3 - E/K) := by ring_nf
          rw [e1, e2]
          exact Real.exp_le_exp.mpr (by linarith)

end TalagrandCore
end

/-! ## Component: Basic -/
section
/-
Core setting for the Talagrand/Ledoux/Klein–Rio development over the finite
Boolean product space `κ → Bool` with the product Bernoulli measure.

Everything here is *finite*: `κ` and `ι` are fintypes, so all functions are
measurable and all integrability is automatic.  The main content of this file:

* `bernPi p hp : Measure (κ → Bool)` — the product Bernoulli measure
  (`Measure.pi` of `(PMF.bernoulli p hp).toMeasure`), exactly as in the
  mission's theorem statements.
* basic instances (probability measure, measurable singletons).
* the finite-sum representation of integrals against `bernPi`.
* the update/Fubini identity: integrating `f (Function.update ω x t)` in
  `(ω, t)` against `bernPi ⊗ bern` equals integrating `f` against `bernPi`.
-/

open MeasureTheory
open scoped BigOperators

namespace TalagrandCore

variable {κ : Type} [DecidableEq κ] [Fintype κ]

/-- The product Bernoulli measure on the Boolean cube indexed by `κ`. -/
noncomputable def bernPi (κ : Type) [Fintype κ] (p : NNReal) (hp : p ≤ 1) :
    Measure (κ → Bool) :=
  Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)

instance (p : NNReal) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernPi κ p hp) := by
  unfold bernPi; infer_instance

/-- On the finite Boolean cube every real-valued function is integrable. -/
theorem integrable_bernPi (p : NNReal) (hp : p ≤ 1) (f : (κ → Bool) → ℝ) :
    Integrable f (bernPi κ p hp) :=
  .of_finite

end TalagrandCore
end

/-! ## Component: SumLand -/
section
/-
Finite-sum representation of expectations over the Boolean product space, and
the pointwise (deterministic) facts about suprema of coordinate processes used
throughout the Talagrand/Ledoux/Klein–Rio development.

`Ex p f = ∑ ω, W p ω * f ω` is the expectation of `f` under the product
Bernoulli(p) weights `W p ω = ∏ x, bw p (ω x)`; the bridge to the
`Measure.pi (fun _ => (PMF.bernoulli p hp).toMeasure)` Bochner integral is
proved in `Bridge.lean`.
-/

open scoped BigOperators

namespace TalagrandCore

/-- Bernoulli point weight on `Bool`. -/
def bw (p : ℝ) : Bool → ℝ := fun b => cond b p (1 - p)

/-- Product Bernoulli weight of a point of the Boolean cube. -/
noncomputable def W {κ : Type} [Fintype κ] (p : ℝ) (ω : κ → Bool) : ℝ :=
  ∏ x : κ, bw p (ω x)

/-- Expectation (finite sum) against the product Bernoulli weights. -/
noncomputable def Ex {κ : Type} [DecidableEq κ] [Fintype κ] (p : ℝ) (f : (κ → Bool) → ℝ) : ℝ :=
  ∑ ω : κ → Bool, W p ω * f ω

variable {κ : Type} [DecidableEq κ] [Fintype κ] {p : ℝ}

theorem bw_nonneg (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∀ b, 0 ≤ bw p b := by
  intro b; cases b <;> simp [bw] <;> linarith

theorem bw_sum (p : ℝ) : bw p true + bw p false = 1 := by simp [bw]

theorem W_nonneg (h0 : 0 ≤ p) (h1 : p ≤ 1) (ω : κ → Bool) : 0 ≤ W p ω :=
  Finset.prod_nonneg fun x _ => bw_nonneg h0 h1 (ω x)

theorem W_sum (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∑ ω : κ → Bool, W p ω = 1 := by
  unfold W
  have h := Finset.prod_univ_sum (fun _ : κ => (Finset.univ : Finset Bool))
      (fun (_ : κ) (b : Bool) => bw p b)
  have huniv :
      (Finset.univ : Finset (κ → Bool)) =
        Fintype.piFinset (fun _ : κ => (Finset.univ : Finset Bool)) :=
    (Fintype.piFinset_univ).symm
  rw [huniv, ← h]
  have hone : ∀ _x : κ, ∑ b : Bool, bw p b = 1 := by
    intro _x; simp [bw]
  calc ∏ x : κ, ∑ b ∈ (Finset.univ : Finset Bool), bw p b
      = ∏ _x : κ, (1 : ℝ) := Finset.prod_congr rfl (fun x _ => hone x)
    _ = 1 := Finset.prod_const_one

/-- `Ex` is monotone. -/
theorem Ex_mono (h0 : 0 ≤ p) (h1 : p ≤ 1) {f g : (κ → Bool) → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : Ex p f ≤ Ex p g :=
  Finset.sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (W_nonneg h0 h1 ω)

theorem Ex_add (f g : (κ → Bool) → ℝ) : Ex p (fun ω => f ω + g ω) = Ex p f + Ex p g := by
  unfold Ex; simp [mul_add, Finset.sum_add_distrib]

theorem Ex_const (h0 : 0 ≤ p) (h1 : p ≤ 1) (c : ℝ) :
    Ex (κ := κ) p (fun _ => c) = c := by
  unfold Ex
  have hws := W_sum (κ := κ) (p := p) h0 h1
  calc ∑ ω : κ → Bool, W p ω * c
      = (∑ ω : κ → Bool, W p ω) * c := by rw [Finset.sum_mul]
    _ = 1 * c := by rw [hws]
    _ = c := one_mul c

/-- Pointwise congruence for `Ex`. -/
theorem Ex_congr {f g : (κ → Bool) → ℝ} (h : ∀ ω, f ω = g ω) :
    Ex p f = Ex p g :=
  Finset.sum_congr rfl fun ω _ => by rw [h ω]

/-- `Ex` commutes with finite sums over another index. -/
theorem Ex_finsum {α : Type} (s : Finset α) (h : α → (κ → Bool) → ℝ) :
    Ex p (fun ω => ∑ a ∈ s, h a ω) = ∑ a ∈ s, Ex p (h a) := by
  unfold Ex
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω _ => by rw [Finset.mul_sum]

theorem Ex_nonneg (h0 : 0 ≤ p) (h1 : p ≤ 1) {f : (κ → Bool) → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ Ex p f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (W_nonneg h0 h1 ω) (hf ω)

/-- Positivity of `Ex` for (pointwise) positive integrands. -/
theorem Ex_pos (h0 : 0 ≤ p) (h1 : p ≤ 1) {f : (κ → Bool) → ℝ}
    (hf : ∀ ω, 0 < f ω) : 0 < Ex p f := by
  classical
  have hW : ∃ ω : κ → Bool, 0 < W p ω := by
    by_contra hno
    push_neg at hno
    have hz : ∀ ω : κ → Bool, W p ω = 0 := fun ω =>
      le_antisymm (hno ω) (W_nonneg h0 h1 ω)
    have := W_sum (κ := κ) h0 h1
    rw [Finset.sum_congr rfl (fun ω _ => hz ω), Finset.sum_const_zero] at this
    norm_num at this
  obtain ⟨ω₀, hω₀⟩ := hW
  refine Finset.sum_pos' (fun ω _ => mul_nonneg (W_nonneg h0 h1 ω) (le_of_lt (hf ω))) ?_
  exact ⟨ω₀, Finset.mem_univ ω₀, mul_pos hω₀ (hf ω₀)⟩

theorem Ex_smul (c : ℝ) (f : (κ → Bool) → ℝ) :
    Ex p (fun ω => c * f ω) = c * Ex p f := by
  unfold Ex
  rw [Finset.mul_sum]; congr 1; ext ω; ring

end TalagrandCore
end

/-! ## Component: Fiber -/
section
/-
Per-coordinate conditional expectation on the Boolean cube, in sum-land.

`condEx p x f ω` is the average of `f` over resampling coordinate `x`
(a function constant in `ω x`).  Key fact: `Ex_condEx` — resampling a
coordinate preserves the product-Bernoulli expectation.
-/

open scoped BigOperators

namespace TalagrandCore

variable {κ : Type} [DecidableEq κ] [Fintype κ] {p : ℝ}

/-- Conditional expectation over coordinate `x` (two-point average). -/
noncomputable def condEx (p : ℝ) (x : κ) (f : (κ → Bool) → ℝ) (ω : κ → Bool) : ℝ :=
  bw p true * f (Function.update ω x true) +
    bw p false * f (Function.update ω x false)

theorem condEx_apply_update (x : κ) (f : (κ → Bool) → ℝ) (ω : κ → Bool) (t : Bool) :
    condEx p x (f := f) (Function.update ω x t) = condEx p x f ω := by
  unfold condEx
  rw [Function.update_idem, Function.update_idem]

/-- `condEx` of a nonnegative function is nonnegative. -/
theorem condEx_nonneg (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : κ) {f : (κ → Bool) → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) (ω : κ → Bool) : 0 ≤ condEx p x f ω := by
  unfold condEx
  have h := bw_nonneg (p := p) h0 h1
  have := hf (Function.update ω x true)
  have := hf (Function.update ω x false)
  nlinarith [h true, h false]

/-- The residual weight of a configuration, ignoring coordinate `x`. -/
noncomputable def Wrest (p : ℝ) (x : κ) (ω : κ → Bool) : ℝ :=
  ∏ y ∈ Finset.univ.erase x, bw p (ω y)

theorem Wrest_update (x : κ) (ω : κ → Bool) (t : Bool) :
    Wrest p x (Function.update ω x t) = Wrest p x ω := by
  unfold Wrest
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hy)]

theorem W_eq_bw_mul_Wrest (x : κ) (ω : κ → Bool) :
    W p ω = bw p (ω x) * Wrest p x ω := by
  unfold W Wrest
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]

/-- Any `x`-fiber-constant reweighted sum localizes to the `ω x = true` slice. -/
theorem sum_W_mul_fiberconst (x : κ) (C : (κ → Bool) → ℝ)
    (hC : ∀ ω t, C (Function.update ω x t) = C ω) :
    ∑ ω : κ → Bool, W p ω * C ω =
      ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true),
        Wrest p x ω * C ω := by
  have hsplit :
      ∑ ω : κ → Bool, W p ω * C ω =
        ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true), W p ω * C ω +
        ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ¬ (ω x = true)), W p ω * C ω :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- On the `false` slice, re-index by flipping coordinate `x` to `true`.
  have hflip :
      ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ¬ (ω x = true)), W p ω * C ω =
        ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true),
          bw p false * (Wrest p x ω * C ω) := by
    refine Finset.sum_nbij' (i := fun ω => Function.update ω x true)
      (j := fun ω => Function.update ω x false) ?_ ?_ ?_ ?_ ?_
    · intro ω hω
      simp [Finset.mem_filter]
    · intro ω hω
      simp [Finset.mem_filter]
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      funext y
      by_cases hy : y = x
      · subst hy
        simp [Function.update_self]
        exact (Bool.not_eq_true _).mp hω
      · simp [Function.update_apply, hy]
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      funext y
      by_cases hy : y = x
      · subst hy; simp [Function.update_self, hω]
      · simp [Function.update_apply, hy]
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      rw [W_eq_bw_mul_Wrest x, hC, Wrest_update]
      have hωx : ω x = false := (Bool.not_eq_true _).mp hω
      rw [hωx]
      ring
  rw [hsplit, hflip]
  have hslice :
      ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true), W p ω * C ω =
        ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true),
          bw p true * (Wrest p x ω * C ω) := by
    refine Finset.sum_congr rfl fun ω hω => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rw [W_eq_bw_mul_Wrest x, hω]
    ring
  rw [hslice, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω hω => ?_
  have hbw := bw_sum p
  calc bw p true * (Wrest p x ω * C ω) + bw p false * (Wrest p x ω * C ω)
      = (bw p true + bw p false) * (Wrest p x ω * C ω) := by ring
    _ = 1 * (Wrest p x ω * C ω) := by rw [hbw]
    _ = Wrest p x ω * C ω := one_mul _

/-- Resampling one coordinate preserves the product-Bernoulli expectation. -/
theorem Ex_condEx (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : κ) (f : (κ → Bool) → ℝ) :
    Ex p (condEx p x f) = Ex p f := by
  -- Both sides localize to the `ω x = true` slice with weight `Wrest·condEx`.
  have hLHS := sum_W_mul_fiberconst (p := p) x (condEx p x f)
    (fun ω t => condEx_apply_update x f ω t)
  -- For the RHS: split, flip the `false` slice, and recombine into `condEx`.
  have hRHS :
      Ex p f =
        ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true),
          Wrest p x ω * condEx p x f ω := by
    unfold Ex
    have hsplit :
        ∑ ω : κ → Bool, W p ω * f ω =
          ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true), W p ω * f ω +
          ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ¬ (ω x = true)), W p ω * f ω :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hflip :
        ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ¬ (ω x = true)), W p ω * f ω =
          ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true),
            bw p false * (Wrest p x ω * f (Function.update ω x false)) := by
      refine Finset.sum_nbij' (i := fun ω => Function.update ω x true)
        (j := fun ω => Function.update ω x false) ?_ ?_ ?_ ?_ ?_
      · intro ω hω
        simp [Finset.mem_filter]
      · intro ω hω
        simp [Finset.mem_filter]
      · intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
        funext y
        by_cases hy : y = x
        · subst hy
          simp [Function.update_self]
          exact (Bool.not_eq_true _).mp hω
        · simp [Function.update_apply, hy]
      · intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
        funext y
        by_cases hy : y = x
        · subst hy; simp [Function.update_self, hω]
        · simp [Function.update_apply, hy]
      · intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
        have hωx : ω x = false := (Bool.not_eq_true _).mp hω
        have hupd : Function.update ω x false = ω := by
          rw [← hωx]; exact Function.update_eq_self x ω
        rw [W_eq_bw_mul_Wrest x, hωx, Wrest_update, Function.update_idem, hupd]
        ring
    have hslice :
        ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true), W p ω * f ω =
          ∑ ω ∈ Finset.univ.filter (fun ω : κ → Bool => ω x = true),
            bw p true * (Wrest p x ω * f (Function.update ω x true)) := by
      refine Finset.sum_congr rfl fun ω hω => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      have hupd : Function.update ω x true = ω := by
        funext y
        by_cases hy : y = x
        · subst hy; simp [Function.update_self, hω]
        · simp [Function.update_apply, hy]
      rw [W_eq_bw_mul_Wrest x, hω, hupd]
      ring
    rw [hsplit, hflip, hslice, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω hω => ?_
    unfold condEx
    ring
  rw [← hRHS] at hLHS
  unfold Ex at hLHS ⊢
  exact hLHS

end TalagrandCore
end

/-! ## Component: Bridge -/
section
/-
Bridges between the `Measure.pi (fun _ => (PMF.bernoulli p hp).toMeasure)`
Bochner integral (the platform's phrasing) and the finite-sum expectation
`Ex`, plus the corresponding bridge for one-coordinate conditional
expectations and for (real-valued) measures of sets.
-/

open MeasureTheory
open scoped BigOperators

namespace TalagrandCore

variable {κ : Type} [DecidableEq κ] [Fintype κ]

theorem bern_toMeasure_singleton (p : NNReal) (hp : p ≤ 1) (b : Bool) :
    ((PMF.bernoulli p hp).toMeasure {b}).toReal = bw (p : ℝ) b := by
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton b)]
  cases b with
  | true => simp [PMF.bernoulli_apply, bw]
  | false =>
      simp only [PMF.bernoulli_apply, bw]
      simp only [Bool.cond_false]
      rw [ENNReal.coe_toReal, NNReal.coe_sub hp, NNReal.coe_one]

/-- Weight of a singleton under the product Bernoulli measure. -/
theorem bernPi_singleton (p : NNReal) (hp : p ≤ 1) (ω : κ → Bool) :
    (bernPi κ p hp).real {ω} = W (p : ℝ) ω := by
  unfold bernPi W
  rw [measureReal_def]
  have hset : ({ω} : Set (κ → Bool)) = Set.univ.pi (fun x => {ω x}) := by
    ext ω'
    simp [Set.mem_pi, funext_iff]
  rw [hset, Measure.pi_pi]
  rw [ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun x _ => bern_toMeasure_singleton p hp (ω x)

/-- Integrals against `bernPi` are the weighted finite sums `Ex`. -/
theorem integral_bernPi_eq_Ex (p : NNReal) (hp : p ≤ 1) (f : (κ → Bool) → ℝ) :
    ∫ ω, f ω ∂(bernPi κ p hp) = Ex (p : ℝ) f := by
  rw [integral_fintype (integrable_bernPi p hp f)]
  unfold Ex
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [bernPi_singleton, smul_eq_mul]

/-- Measure (real-valued) of a set as an `Ex` of its indicator. -/
theorem bernPi_real_eq_Ex_indicator (p : NNReal) (hp : p ≤ 1)
    (S : Set (κ → Bool)) :
    (bernPi κ p hp).real S =
      Ex (p : ℝ) (fun ω => S.indicator (fun _ => (1:ℝ)) ω) := by
  have hmeas : MeasurableSet S := (Set.toFinite S).measurableSet
  have h1 : (bernPi κ p hp).real S = ∫ ω, S.indicator (fun _ => (1:ℝ)) ω ∂(bernPi κ p hp) := by
    rw [integral_indicator hmeas]
    simp [measureReal_def]
  rw [h1, integral_bernPi_eq_Ex]

/-- The one-coordinate fiber integral over `Bern(p)` is `condEx`. -/
theorem integral_bernoulli_update_eq_condEx (p : NNReal) (hp : p ≤ 1)
    (x : κ) (f : (κ → Bool) → ℝ) (ω : κ → Bool) :
    ∫ t, f (Function.update ω x t) ∂((PMF.bernoulli p hp).toMeasure) =
      condEx (p : ℝ) x f ω := by
  rw [PMF.integral_eq_sum]
  rw [Fintype.sum_bool]
  unfold condEx
  have ht := bern_toMeasure_singleton p hp true
  have hf := bern_toMeasure_singleton p hp false
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton true)] at ht
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton false)] at hf
  rw [ht, hf, smul_eq_mul, smul_eq_mul]

/-- Plain Bernoulli two-point integral (no update). -/
theorem integral_bernoulli_eq (p : NNReal) (hp : p ≤ 1) (h : Bool → ℝ) :
    ∫ t, h t ∂((PMF.bernoulli p hp).toMeasure) =
      bw (p : ℝ) true * h true + bw (p : ℝ) false * h false := by
  rw [PMF.integral_eq_sum, Fintype.sum_bool]
  have ht := bern_toMeasure_singleton p hp true
  have hf := bern_toMeasure_singleton p hp false
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton true)] at ht
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton false)] at hf
  rw [ht, hf, smul_eq_mul, smul_eq_mul]

end TalagrandCore
end

/-! ## Component: Entropy -/
section
/-
The master tensorized entropy inequality on the Boolean cube.

* The per-fiber ψ-bound is proved directly from `log x ≤ x − 1`
  (the two-point case of the Massart variational bound).
* Tensorization comes from the platform's Han subadditivity brick
  (`entropy_n_coordinate_han_subadditivity_measure_pi_pos`, indexed by
  `Fin n`), transported to a generic fintype `κ` in sum-land.

Master inequality: for any `Z`, `lam ∈ ℝ`, and any family
`c : κ → (κ → Bool) → ℝ` with `c x` constant along the `x`-fiber,

  Ex[lam·Z·e^{lam Z}] − Ex[e^{lam Z}]·log Ex[e^{lam Z}]
    ≤ ∑ x, Ex[e^{lam Z} · ψ(lam·(Z − c x))],   ψ(u) = e^{−u} − 1 + u.
-/

open MeasureTheory
open scoped BigOperators

namespace TalagrandCore

variable {κ : Type} [DecidableEq κ] [Fintype κ]

/-- ψ(u) = e^{−u} − 1 + u, the entropy-method kernel. -/
noncomputable def psi (u : ℝ) : ℝ := Real.exp (-u) - 1 + u

/-- A function is `x`-fiber constant if it does not depend on coordinate `x`. -/
def FiberConst (x : κ) (c : (κ → Bool) → ℝ) : Prop :=
  ∀ ω t, c (Function.update ω x t) = c ω

/-- Two-point variational entropy bound (the fiber ψ-inequality), proved from
`log x ≤ x − 1`:  for weights `a + b = 1`, `a, b ≥ 0`, values `Z₁ Z₂` and any
constant `c₀`,

  lam(a Z₁ G₁ + b Z₂ G₂) − S log S ≤ a G₁ ψ(lam(Z₁−c₀)) + b G₂ ψ(lam(Z₂−c₀))

where `Gᵢ = e^{lam Zᵢ}` and `S = a G₁ + b G₂`. -/
theorem two_point_psi_bound (a b Z₁ Z₂ c₀ lam : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    lam * (a * (Z₁ * Real.exp (lam * Z₁)) + b * (Z₂ * Real.exp (lam * Z₂))) -
      (a * Real.exp (lam * Z₁) + b * Real.exp (lam * Z₂)) *
        Real.log (a * Real.exp (lam * Z₁) + b * Real.exp (lam * Z₂)) ≤
      a * (Real.exp (lam * Z₁) * psi (lam * (Z₁ - c₀))) +
        b * (Real.exp (lam * Z₂) * psi (lam * (Z₂ - c₀))) := by
  set G₁ := Real.exp (lam * Z₁) with hG₁
  set G₂ := Real.exp (lam * Z₂) with hG₂
  set S := a * G₁ + b * G₂ with hS
  set u := Real.exp (lam * c₀) with hu
  have hG₁pos : 0 < G₁ := Real.exp_pos _
  have hG₂pos : 0 < G₂ := Real.exp_pos _
  have hupos : 0 < u := Real.exp_pos _
  have hSpos : 0 < S := by
    rcases eq_or_lt_of_le ha with h | h
    · have hb1 : b = 1 := by linarith
      rw [hS, ← h, hb1]; simpa using hG₂pos
    · have : 0 < a * G₁ := mul_pos h hG₁pos
      nlinarith [mul_nonneg hb hG₂pos.le]
  -- Expand ψ:  Gᵢ·ψ(lam(Zᵢ−c₀)) = u − Gᵢ + lam Zᵢ Gᵢ − lam c₀ Gᵢ.
  have hexp₁ : G₁ * psi (lam * (Z₁ - c₀)) =
      u - G₁ + lam * Z₁ * G₁ - lam * c₀ * G₁ := by
    unfold psi
    rw [hG₁, hu]
    have : Real.exp (lam * Z₁) * Real.exp (-(lam * (Z₁ - c₀))) =
        Real.exp (lam * c₀) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [this]
  have hexp₂ : G₂ * psi (lam * (Z₂ - c₀)) =
      u - G₂ + lam * Z₂ * G₂ - lam * c₀ * G₂ := by
    unfold psi
    rw [hG₂, hu]
    have : Real.exp (lam * Z₂) * Real.exp (-(lam * (Z₂ - c₀))) =
        Real.exp (lam * c₀) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [this]
  -- log(u/S) ≤ u/S − 1  ⟺  S log u − S log S ≤ u − S.
  have hlog : Real.log (u / S) ≤ u / S - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlogdiv : Real.log (u / S) = Real.log u - Real.log S :=
    Real.log_div (ne_of_gt hupos) (ne_of_gt hSpos)
  have hlogu : Real.log u = lam * c₀ := by rw [hu, Real.log_exp]
  have key : S * Real.log u - S * Real.log S ≤ u - S := by
    have h1 : S * Real.log (u / S) ≤ S * (u / S - 1) :=
      mul_le_mul_of_nonneg_left hlog hSpos.le
    have h2 : S * (u / S - 1) = u - S := by field_simp
    rw [hlogdiv] at h1
    nlinarith [h1]
  rw [hexp₁, hexp₂] at *
  rw [hlogu] at key
  nlinarith [key]

/-- Fiber-entropy bound at coordinate `x` (pointwise in `ω`). -/
theorem fiber_entropy_le_psi (p : NNReal) (hp : p ≤ 1) (x : κ)
    (Z : (κ → Bool) → ℝ) (lam : ℝ) (c : (κ → Bool) → ℝ) (hc : FiberConst x c)
    (ω : κ → Bool) :
    lam * condEx (p : ℝ) x (fun ω' => Z ω' * Real.exp (lam * Z ω')) ω -
      condEx (p : ℝ) x (fun ω' => Real.exp (lam * Z ω')) ω *
        Real.log (condEx (p : ℝ) x (fun ω' => Real.exp (lam * Z ω')) ω) ≤
      condEx (p : ℝ) x
        (fun ω' => Real.exp (lam * Z ω') * psi (lam * (Z ω' - c ω'))) ω := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have := two_point_psi_bound (bw (p:ℝ) true) (bw (p:ℝ) false)
    (Z (Function.update ω x true)) (Z (Function.update ω x false)) (c ω) lam
    (bw_nonneg h0p h1p true) (bw_nonneg h0p h1p false) (bw_sum (p:ℝ))
  unfold condEx
  simp only
  have e1 : c (Function.update ω x true) = c ω := hc ω true
  have e2 : c (Function.update ω x false) = c ω := hc ω false
  rw [e1, e2]
  exact this

/-- Sum-land reindexing of `Ex` along an equivalence of index types
(pointwise-hypothesis form, robust to beta-reduction). -/
theorem Ex_reindex {n : ℕ} (e : κ ≃ Fin n) (q : ℝ)
    (f : (κ → Bool) → ℝ) (g : (Fin n → Bool) → ℝ)
    (h : ∀ η, g η = f (fun x => η (e x))) :
    Ex (κ := Fin n) q g = Ex (κ := κ) q f := by
  unfold Ex W
  refine Finset.sum_nbij' (i := fun (η : Fin n → Bool) => (fun x => η (e x)))
    (j := fun (ω : κ → Bool) => (fun k => ω (e.symm k))) ?_ ?_ ?_ ?_ ?_
  · intro η _; exact Finset.mem_univ _
  · intro ω _; exact Finset.mem_univ _
  · intro η _
    funext k
    simp [Equiv.apply_symm_apply]
  · intro ω _
    funext x
    simp [Equiv.symm_apply_apply]
  · intro η _
    rw [h η]
    congr 1
    exact (Fintype.prod_equiv e (fun x : κ => bw q (η (e x)))
      (fun i : Fin n => bw q (η i)) (fun x => rfl)).symm

/-- Update transports along the reindexing. -/
theorem update_reindex {n : ℕ} (e : κ ≃ Fin n) (η : Fin n → Bool) (k : Fin n) (t : Bool) :
    (fun x => (Function.update η k t) (e x)) =
      Function.update (fun x => η (e x)) (e.symm k) t := by
  funext x
  rw [Function.update_apply, Function.update_apply]
  by_cases hx : e x = k
  · rw [if_pos hx, if_pos (by rw [← hx, Equiv.symm_apply_apply])]
  · rw [if_neg hx, if_neg (fun hxx => hx (by rw [hxx, Equiv.apply_symm_apply]))]

/-- Plain tensorization (Han transported to sum-land): for positive `G`,

  Ent(G) ≤ ∑_x ( Ex[G log G] − Ex[(condEx x G)·log (condEx x G)] ). -/
theorem entropy_tensor_log (p : NNReal) (hp : p ≤ 1)
    (G : (κ → Bool) → ℝ) (hG : ∀ ω, 0 < G ω) :
    Ex (p : ℝ) (fun ω => G ω * Real.log (G ω)) -
      Ex (p : ℝ) G * Real.log (Ex (p : ℝ) G) ≤
      ∑ x : κ, (Ex (p : ℝ) (fun ω => G ω * Real.log (G ω)) -
        Ex (p : ℝ) (fun ω => condEx (p : ℝ) x G ω *
          Real.log (condEx (p : ℝ) x G ω))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set n := Fintype.card κ with hn
  set e : κ ≃ Fin n := Fintype.equivFin κ with he
  set r : (Fin n → Bool) → (κ → Bool) := fun η x => η (e x) with hr
  set G' : (Fin n → Bool) → ℝ := fun η => G (r η) with hG'
  have hG'pos : ∀ η, 0 < G' η := fun η => hG (r η)
  have hne : (Finset.univ : Finset (Fin n → Bool)).Nonempty := Finset.univ_nonempty
  set cc : ℝ := Finset.univ.inf' hne G' with hcc
  set CC : ℝ := Finset.univ.sup' hne G' with hCC
  have hccpos : 0 < cc := by
    rw [hcc, Finset.lt_inf'_iff]
    exact fun η _ => hG'pos η
  have hccle : ∀ η, cc ≤ G' η := fun η => Finset.inf'_le _ (Finset.mem_univ η)
  have hCCge : ∀ η, G' η ≤ CC := fun η => Finset.le_sup' _ (Finset.mem_univ η)
  have hG'meas : Measurable G' := measurable_of_countable _
  have han := entropy_n_coordinate_han_subadditivity_measure_pi_pos
    (μ := fun _ : Fin n => (PMF.bernoulli p hp).toMeasure) G' cc CC hccpos hG'meas hccle hCCge
  have hpi : (Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure) =
      bernPi (Fin n) p hp := rfl
  have hEx : (∫ η, G' η ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) =
      Ex (p : ℝ) G := by
    rw [hpi, integral_bernPi_eq_Ex p hp G']
    exact Ex_reindex e (p : ℝ) G G' (fun η => rfl)
  have hExlog : (∫ η, G' η * Real.log (G' η)
        ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) =
      Ex (p : ℝ) (fun ω => G ω * Real.log (G ω)) := by
    rw [hpi, integral_bernPi_eq_Ex p hp (fun η => G' η * Real.log (G' η))]
    exact Ex_reindex e (p : ℝ) (fun ω => G ω * Real.log (G ω))
      (fun η => G' η * Real.log (G' η)) (fun η => rfl)
  have hterm : ∀ k : Fin n,
      (∫ η, (∫ t, G' (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure)) *
          Real.log (∫ t, G' (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure))
        ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) =
      Ex (p : ℝ) (fun ω => condEx (p : ℝ) (e.symm k) G ω *
        Real.log (condEx (p : ℝ) (e.symm k) G ω)) := by
    intro k
    set x₀ : κ := e.symm k with hx₀
    have hru : ∀ (η : Fin n → Bool) (t : Bool),
        r (Function.update η k t) = Function.update (r η) x₀ t := by
      intro η t
      rw [hr, hx₀]
      exact update_reindex e η k t
    have hinner : ∀ η : Fin n → Bool,
        (∫ t, G' (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure)) =
          condEx (p : ℝ) x₀ G (r η) := by
      intro η
      rw [integral_bernoulli_eq p hp]
      unfold condEx
      have h₁ : G' (Function.update η k true) = G (Function.update (r η) x₀ true) := by
        show G (r (Function.update η k true)) = _
        rw [hru η true]
      have h₂ : G' (Function.update η k false) = G (Function.update (r η) x₀ false) := by
        show G (r (Function.update η k false)) = _
        rw [hru η false]
      rw [h₁, h₂]
    rw [hpi, integral_bernPi_eq_Ex p hp]
    exact Ex_reindex e (p : ℝ)
      (fun ω => condEx (p : ℝ) x₀ G ω * Real.log (condEx (p : ℝ) x₀ G ω))
      (fun η => (∫ t, G' (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure)) *
        Real.log (∫ t, G' (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure)))
      (fun η => by rw [hinner η])
  calc Ex (p : ℝ) (fun ω => G ω * Real.log (G ω)) -
        Ex (p : ℝ) G * Real.log (Ex (p : ℝ) G)
      = (∫ η, G' η * Real.log (G' η)
            ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) -
          (∫ η, G' η ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) *
            Real.log (∫ η, G' η
              ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) := by
        rw [hEx, hExlog]
    _ ≤ _ := han
    _ = ∑ k : Fin n, (Ex (p : ℝ) (fun ω => G ω * Real.log (G ω)) -
          Ex (p : ℝ) (fun ω => condEx (p : ℝ) (e.symm k) G ω *
            Real.log (condEx (p : ℝ) (e.symm k) G ω))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hExlog, hterm k]
    _ = ∑ x : κ, (Ex (p : ℝ) (fun ω => G ω * Real.log (G ω)) -
          Ex (p : ℝ) (fun ω => condEx (p : ℝ) x G ω *
            Real.log (condEx (p : ℝ) x G ω))) :=
        Fintype.sum_equiv e.symm _ _ fun k => rfl

/-- Master tensorized entropy inequality (Han + per-fiber ψ). -/
theorem entropy_tensor_psi (p : NNReal) (hp : p ≤ 1)
    (Z : (κ → Bool) → ℝ) (lam : ℝ)
    (c : κ → (κ → Bool) → ℝ) (hc : ∀ x, FiberConst x (c x)) :
    lam * Ex (p : ℝ) (fun ω => Z ω * Real.exp (lam * Z ω)) -
      Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω)) *
        Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω))) ≤
      ∑ x : κ, Ex (p : ℝ)
        (fun ω => Real.exp (lam * Z ω) * psi (lam * (Z ω - c x ω))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set n := Fintype.card κ with hn
  set e : κ ≃ Fin n := Fintype.equivFin κ with he
  set r : (Fin n → Bool) → (κ → Bool) := fun η x => η (e x) with hr
  set G : (Fin n → Bool) → ℝ := fun η => Real.exp (lam * Z (r η)) with hG
  have hGpos : ∀ η, 0 < G η := fun η => Real.exp_pos _
  have hne : (Finset.univ : Finset (Fin n → Bool)).Nonempty := Finset.univ_nonempty
  set cc : ℝ := Finset.univ.inf' hne G with hcc
  set CC : ℝ := Finset.univ.sup' hne G with hCC
  have hccpos : 0 < cc := by
    rw [hcc, Finset.lt_inf'_iff]
    exact fun η _ => hGpos η
  have hccle : ∀ η, cc ≤ G η := fun η => Finset.inf'_le _ (Finset.mem_univ η)
  have hCCge : ∀ η, G η ≤ CC := fun η => Finset.le_sup' _ (Finset.mem_univ η)
  have hGmeas : Measurable G := measurable_of_countable _
  have han := entropy_n_coordinate_han_subadditivity_measure_pi_pos
    (μ := fun _ : Fin n => (PMF.bernoulli p hp).toMeasure) G cc CC hccpos hGmeas hccle hCCge
  -- Bridge: full-space integrals to `Ex` over κ.
  have hpi : (Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure) =
      bernPi (Fin n) p hp := rfl
  have hEx : (∫ η, G η ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) =
      Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω)) := by
    rw [hpi, integral_bernPi_eq_Ex p hp G]
    exact Ex_reindex e (p : ℝ) (fun ω => Real.exp (lam * Z ω)) G (fun η => rfl)
  have hExlog : (∫ η, G η * Real.log (G η)
        ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) =
      lam * Ex (p : ℝ) (fun ω => Z ω * Real.exp (lam * Z ω)) := by
    rw [hpi, integral_bernPi_eq_Ex p hp (fun η => G η * Real.log (G η))]
    rw [← Ex_smul]
    exact Ex_reindex e (p : ℝ)
      (fun ω => lam * (Z ω * Real.exp (lam * Z ω)))
      (fun η => G η * Real.log (G η))
      (fun η => by rw [hG]; simp only [Real.log_exp]; ring)
  -- Per-coordinate bound.
  have hterm : ∀ k : Fin n,
      (lam * Ex (p : ℝ) (fun ω => Z ω * Real.exp (lam * Z ω)) -
        (∫ η, (∫ t, G (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure)) *
            Real.log (∫ t, G (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure))
          ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure))) ≤
      Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω) *
        psi (lam * (Z ω - c (e.symm k) ω))) := by
    intro k
    set x₀ : κ := e.symm k with hx₀
    -- The inner Bernoulli integral equals `condEx` at the transported point.
    have hinner : ∀ η : Fin n → Bool,
        (∫ t, G (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure)) =
          condEx (p : ℝ) x₀ (fun ω => Real.exp (lam * Z ω)) (r η) := by
      intro η
      rw [integral_bernoulli_eq p hp]
      unfold condEx
      have hru : ∀ t : Bool, r (Function.update η k t) = Function.update (r η) x₀ t := by
        intro t
        rw [hr, hx₀]
        exact update_reindex e η k t
      have h₁ : G (Function.update η k true) =
          Real.exp (lam * Z (Function.update (r η) x₀ true)) := by
        show Real.exp (lam * Z (r (Function.update η k true))) = _
        rw [hru true]
      have h₂ : G (Function.update η k false) =
          Real.exp (lam * Z (Function.update (r η) x₀ false)) := by
        show Real.exp (lam * Z (r (Function.update η k false))) = _
        rw [hru false]
      rw [h₁, h₂]
    -- Outer integral of the (E_k G)·log(E_k G) term, bridged and transported.
    have houter : (∫ η,
          (∫ t, G (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure)) *
            Real.log (∫ t, G (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure))
          ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) =
        Ex (p : ℝ) (fun ω =>
          condEx (p : ℝ) x₀ (fun ω' => Real.exp (lam * Z ω')) ω *
            Real.log (condEx (p : ℝ) x₀ (fun ω' => Real.exp (lam * Z ω')) ω)) := by
      rw [hpi, integral_bernPi_eq_Ex p hp]
      exact Ex_reindex e (p : ℝ)
        (fun ω => condEx (p : ℝ) x₀ (fun ω' => Real.exp (lam * Z ω')) ω *
          Real.log (condEx (p : ℝ) x₀ (fun ω' => Real.exp (lam * Z ω')) ω))
        (fun η => (∫ t, G (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure)) *
          Real.log (∫ t, G (Function.update η k t) ∂((PMF.bernoulli p hp).toMeasure)))
        (fun η => by rw [hinner η])
    rw [houter]
    -- Move the full-entropy piece under `condEx` and conclude pointwise.
    have hfull : lam * Ex (p : ℝ) (fun ω => Z ω * Real.exp (lam * Z ω)) =
        Ex (p : ℝ) (fun ω => lam *
          condEx (p : ℝ) x₀ (fun ω' => Z ω' * Real.exp (lam * Z ω')) ω) := by
      rw [← Ex_condEx h0p h1p x₀ (fun ω' => Z ω' * Real.exp (lam * Z ω')), ← Ex_smul]
    have hpsi : Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω) *
          psi (lam * (Z ω - c x₀ ω))) =
        Ex (p : ℝ) (fun ω => condEx (p : ℝ) x₀
          (fun ω' => Real.exp (lam * Z ω') * psi (lam * (Z ω' - c x₀ ω'))) ω) := by
      rw [Ex_condEx h0p h1p x₀]
    rw [hfull, hpsi]
    have hcomb : Ex (p:ℝ) (fun ω => lam *
          condEx (p : ℝ) x₀ (fun ω' => Z ω' * Real.exp (lam * Z ω')) ω) -
        Ex (p:ℝ) (fun ω =>
          condEx (p : ℝ) x₀ (fun ω' => Real.exp (lam * Z ω')) ω *
            Real.log (condEx (p : ℝ) x₀ (fun ω' => Real.exp (lam * Z ω')) ω)) =
        Ex (p:ℝ) (fun ω =>
          lam * condEx (p : ℝ) x₀ (fun ω' => Z ω' * Real.exp (lam * Z ω')) ω -
          condEx (p : ℝ) x₀ (fun ω' => Real.exp (lam * Z ω')) ω *
            Real.log (condEx (p : ℝ) x₀ (fun ω' => Real.exp (lam * Z ω')) ω)) := by
      unfold Ex
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ω _ => by ring
    rw [hcomb]
    exact Ex_mono h0p h1p fun ω =>
      fiber_entropy_le_psi p hp x₀ Z lam (c x₀) (hc x₀) ω
  -- Assemble.
  calc lam * Ex (p : ℝ) (fun ω => Z ω * Real.exp (lam * Z ω)) -
        Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω)) *
          Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω)))
      = (∫ η, G η * Real.log (G η)
            ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) -
          (∫ η, G η ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) *
            Real.log (∫ η, G η
              ∂(Measure.pi fun _ : Fin n => (PMF.bernoulli p hp).toMeasure)) := by
        rw [hEx, hExlog]
    _ ≤ _ := han
    _ ≤ ∑ k : Fin n, Ex (p : ℝ)
          (fun ω => Real.exp (lam * Z ω) * psi (lam * (Z ω - c (e.symm k) ω))) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h := hterm k
        rw [← hExlog] at h
        exact h
    _ = ∑ x : κ, Ex (p : ℝ)
          (fun ω => Real.exp (lam * Z ω) * psi (lam * (Z ω - c x ω))) :=
        Fintype.sum_equiv e.symm _ _ fun k => rfl

end TalagrandCore
end

/-! ## Component: Process -/
section
/-
The coordinate processes and their pointwise (deterministic) structure.

* `procSum g ω = ∑ x, g a x (ω x)`-family suprema `supProc`, with leave-one-out
  versions and the self-bounding facts for nonnegative summands (used by the
  self-bounding block T1);
* the linear (Candès–Romberg) process `linProc coeff p`, its supremum `Zp`,
  absolute supremum `Zbar`, and the random variance process `Sigma2`;
* one-coordinate Lipschitz bounds via the two-argmax trick (used by T2).
-/

open scoped BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-! ### Generic supremum process -/

/-- Supremum over `ι` of coordinate sums `∑ x, g a x (ω x)`. -/
noncomputable def supProc (g : ι → κ → Bool → ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι => ∑ x : κ, g a x (ω x))

/-- Leave-one-out supremum process (coordinate `x₀` removed). -/
noncomputable def supProcErase (g : ι → κ → Bool → ℝ) (x₀ : κ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => ∑ x ∈ Finset.univ.erase x₀, g a x (ω x))

theorem supProc_exists_argmax (g : ι → κ → Bool → ℝ) (ω : κ → Bool) :
    ∃ a : ι, supProc g ω = ∑ x : κ, g a x (ω x) := by
  obtain ⟨a, -, ha⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι))
      (fun a : ι => ∑ x : κ, g a x (ω x))
  exact ⟨a, ha⟩

theorem le_supProc (g : ι → κ → Bool → ℝ) (ω : κ → Bool) (a : ι) :
    ∑ x : κ, g a x (ω x) ≤ supProc g ω := by
  unfold supProc
  exact Finset.le_sup' (f := fun a : ι => ∑ x : κ, g a x (ω x)) (Finset.mem_univ a)

theorem le_supProcErase (g : ι → κ → Bool → ℝ) (x₀ : κ) (ω : κ → Bool) (a : ι) :
    ∑ x ∈ Finset.univ.erase x₀, g a x (ω x) ≤ supProcErase g x₀ ω := by
  unfold supProcErase
  exact Finset.le_sup'
    (f := fun a : ι => ∑ x ∈ Finset.univ.erase x₀, g a x (ω x)) (Finset.mem_univ a)

/-- `supProcErase` does not depend on the removed coordinate. -/
theorem supProcErase_update (g : ι → κ → Bool → ℝ) (x₀ : κ) (ω : κ → Bool) (t : Bool) :
    supProcErase g x₀ (Function.update ω x₀ t) = supProcErase g x₀ ω := by
  unfold supProcErase
  congr 1
  funext a
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Function.update_apply]
  rw [if_neg (Finset.ne_of_mem_erase hx)]

/-! ### Self-bounding facts for nonnegative summands -/

section Nonneg
variable {g : ι → κ → Bool → ℝ}

theorem supProcErase_le_supProc (hg0 : ∀ a x b, 0 ≤ g a x b) (x₀ : κ) (ω : κ → Bool) :
    supProcErase g x₀ ω ≤ supProc g ω := by
  apply Finset.sup'_le
  intro a _
  refine le_trans ?_ (le_supProc g ω a)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
  exact fun x _ _ => hg0 a x (ω x)

theorem supProc_sub_supProcErase_le (hg1 : ∀ a x b, g a x b ≤ 1) (x₀ : κ) (ω : κ → Bool) :
    supProc g ω - supProcErase g x₀ ω ≤ 1 := by
  obtain ⟨a, ha⟩ := supProc_exists_argmax g ω
  have h1 : ∑ x : κ, g a x (ω x) =
      g a x₀ (ω x₀) + ∑ x ∈ Finset.univ.erase x₀, g a x (ω x) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)]
  have h2 := le_supProcErase g x₀ ω a
  have h3 := hg1 a x₀ (ω x₀)
  rw [h1] at ha
  linarith

/-- Self-bounding: the sum of the leave-one-out gaps is at most `Y` itself
(for nonnegative summands). -/
theorem sum_supProc_sub_supProcErase_le (hg0 : ∀ a x b, 0 ≤ g a x b) (ω : κ → Bool) :
    ∑ x₀ : κ, (supProc g ω - supProcErase g x₀ ω) ≤ supProc g ω := by
  obtain ⟨a, ha⟩ := supProc_exists_argmax g ω
  have hterm : ∀ x₀ : κ, supProc g ω - supProcErase g x₀ ω ≤ g a x₀ (ω x₀) := by
    intro x₀
    have h2 := le_supProcErase g x₀ ω a
    have hsum : g a x₀ (ω x₀) + ∑ x ∈ Finset.univ.erase x₀, g a x (ω x) =
        ∑ x : κ, g a x (ω x) :=
      Finset.add_sum_erase _ (fun x => g a x (ω x)) (Finset.mem_univ x₀)
    have := ha
    linarith
  calc ∑ x₀ : κ, (supProc g ω - supProcErase g x₀ ω)
      ≤ ∑ x₀ : κ, g a x₀ (ω x₀) := Finset.sum_le_sum fun x₀ _ => hterm x₀
    _ = supProc g ω := ha.symm

end Nonneg

/-! ### The linear (Candès–Romberg) process -/

/-- The centered linear summand `((ω x : 1/0) − p)·c a x`. -/
def linSummand (coeff : ι → κ → ℝ) (p : ℝ) : ι → κ → Bool → ℝ :=
  fun a x b => (cond b (1 : ℝ) 0 - p) * coeff a x

/-- `Z = max_a ∑_x ((ω x) − p) c_a(x)`. -/
noncomputable def Zproc (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) : ℝ :=
  supProc (linSummand coeff p) ω

/-- `Z̄ = max_a |∑_x ((ω x) − p) c_a(x)|`. -/
noncomputable def Zbar (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => |∑ x : κ, (cond (ω x) (1 : ℝ) 0 - p) * coeff a x|)

/-- The random variance process `Σ² = max_a ∑_x c_a(x)²((ω x) − p)²`. -/
noncomputable def Sigma2 (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1 : ℝ) 0 - p) ^ 2)

/-- One-coordinate two-argmax Lipschitz bound for the linear supremum:
changing coordinate `x` from `ω` to `ω' = update ω x t` moves `Z` by at most
`|ωx − t|·max(|c_{a*(ω)}(x)|, |c_{a*(ω')}(x)|)`, and in particular the move is
bounded by the coefficient of the argmax at either endpoint. -/
theorem Zproc_update_le (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) (x : κ) (t : Bool)
    (a : ι) (ha : Zproc coeff p ω = ∑ y : κ, (cond (ω y) (1:ℝ) 0 - p) * coeff a y) :
    Zproc coeff p ω - Zproc coeff p (Function.update ω x t) ≤
      (cond (ω x) (1:ℝ) 0 - cond t 1 0) * coeff a x := by
  have h1 : ∑ y : κ, (cond ((Function.update ω x t) y) (1:ℝ) 0 - p) * coeff a y ≤
      Zproc coeff p (Function.update ω x t) := by
    have := le_supProc (linSummand coeff p) (Function.update ω x t) a
    simpa [Zproc, linSummand] using this
  have hdiff :
      (∑ y : κ, (cond (ω y) (1:ℝ) 0 - p) * coeff a y) -
        (∑ y : κ, (cond ((Function.update ω x t) y) (1:ℝ) 0 - p) * coeff a y) =
      (cond (ω x) (1:ℝ) 0 - cond t 1 0) * coeff a x := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single x]
    · rw [Function.update_self]
      ring
    · intro y _ hy
      rw [Function.update_apply, if_neg hy]
      ring
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  linarith

end TalagrandCore
end

/-! ## Component: SelfBounding -/
section
/-
Block T1: the self-bounding mgf bound for suprema of nonnegative bounded
coordinate sums on the Boolean cube (Ledoux ESAIM'96, machinery of Thm 2.4).

For `g : ι → κ → Bool → ℝ` with `0 ≤ g ≤ 1` and
`Y ω = max_a ∑_x g a x (ω x)`:

  `log Ex[e^{lam·Y}] ≤ Ex[Y] · (e^lam − 1)`  for every `lam ≥ 0`.
-/

open scoped BigOperators

namespace TalagrandCore

open Real

/-- ψ is nonnegative. -/
theorem psi_nonneg (u : ℝ) : 0 ≤ psi u := by
  unfold psi
  nlinarith [Real.add_one_le_exp (-u)]

/-- Convexity bound: `ψ(lam·y) ≤ y·ψ(lam)` for `y ∈ [0,1]`. -/
theorem psi_convex_bound (lam y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    psi (lam * y) ≤ y * psi lam := by
  -- Two-point convexity of `exp`: e^{−lam·y} ≤ y·e^{−lam} + (1−y).
  have key := convexOn_exp.2 (Set.mem_univ (-lam)) (Set.mem_univ (0:ℝ))
    hy0 (by linarith : (0:ℝ) ≤ 1 - y) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at key
  have harg : y * -lam = -(lam * y) := by ring
  rw [harg] at key
  unfold psi
  nlinarith [key]

/-- Derivative of the mgf `F(lam) = Ex[e^{lam Y}]`. -/
theorem hasDerivAt_ExExp {κ : Type} [DecidableEq κ] [Fintype κ] (p : ℝ) (Y : (κ → Bool) → ℝ) (lam : ℝ) :
    HasDerivAt (fun l => Ex p (fun ω => Real.exp (l * Y ω)))
      (Ex p (fun ω => Y ω * Real.exp (lam * Y ω))) lam := by
  unfold Ex
  have : ∀ ω ∈ (Finset.univ : Finset (κ → Bool)),
      HasDerivAt (fun l => W p ω * Real.exp (l * Y ω))
        (W p ω * (Y ω * Real.exp (lam * Y ω))) lam := by
    intro ω _
    have h1 : HasDerivAt (fun l : ℝ => l * Y ω) (Y ω) lam := hasDerivAt_mul_const (Y ω)
    have h2 := (h1.exp).const_mul (W p ω)
    exact h2.congr_deriv (by ring)
  exact HasDerivAt.fun_sum this

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-- **T1 (self-bounding cgf bound).** -/
theorem selfbounding_mgf_bound (p : NNReal) (hp : p ≤ 1)
    (g : ι → κ → Bool → ℝ) (hg0 : ∀ a x b, 0 ≤ g a x b) (hg1 : ∀ a x b, g a x b ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * supProc g ω))) ≤
      Ex (p : ℝ) (fun ω => supProc g ω) * (Real.exp lam - 1) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set Y : (κ → Bool) → ℝ := supProc g with hY
  set F : ℝ → ℝ := fun l => Ex (p : ℝ) (fun ω => Real.exp (l * Y ω)) with hF
  set Gd : ℝ → ℝ := fun l => Ex (p : ℝ) (fun ω => Y ω * Real.exp (l * Y ω)) with hGd
  set EY : ℝ := Ex (p : ℝ) (fun ω => Y ω) with hEY
  have hFpos : ∀ l, 0 < F l := fun l => Ex_pos h0p h1p (fun ω => Real.exp_pos _)
  have hFderiv : ∀ l, HasDerivAt F (Gd l) l := fun l => hasDerivAt_ExExp (p : ℝ) Y l
  have hF0 : F 0 = 1 := by
    show Ex (p : ℝ) (fun ω => Real.exp ((0:ℝ) * Y ω)) = 1
    have h1 : (fun ω : κ → Bool => Real.exp ((0:ℝ) * Y ω)) = fun _ => (1:ℝ) := by
      funext ω; simp
    rw [h1, Ex_const h0p h1p]
  -- The entropy differential inequality: (l − ψ(l))·Gd l ≤ F l · log (F l), l ≥ 0.
  have hDI : ∀ l, 0 ≤ l → (1 - Real.exp (-l)) * Gd l ≤ F l * Real.log (F l) := by
    intro l hl
    have master := entropy_tensor_psi p hp Y l (fun x => supProcErase g x)
      (fun x ω t => supProcErase_update g x ω t)
    -- Pointwise: ψ(l(Y−Yx)) ≤ (Y−Yx)ψ(l), sum ≤ Y·ψ(l).
    have hsum_le : ∑ x : κ, Ex (p : ℝ)
          (fun ω => Real.exp (l * Y ω) * psi (l * (Y ω - supProcErase g x ω))) ≤
        Ex (p : ℝ) (fun ω => Real.exp (l * Y ω) * (Y ω * psi l)) := by
      rw [← Ex_finsum]
      apply Ex_mono h0p h1p
      intro ω
      have hpt : ∀ x : κ, Real.exp (l * Y ω) * psi (l * (Y ω - supProcErase g x ω)) ≤
          Real.exp (l * Y ω) * ((Y ω - supProcErase g x ω) * psi l) := by
        intro x
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact psi_convex_bound l _
          (by linarith [supProcErase_le_supProc hg0 x ω])
          (supProc_sub_supProcErase_le hg1 x ω)
      calc ∑ x : κ, Real.exp (l * Y ω) * psi (l * (Y ω - supProcErase g x ω))
          ≤ ∑ x : κ, Real.exp (l * Y ω) * ((Y ω - supProcErase g x ω) * psi l) :=
            Finset.sum_le_sum fun x _ => hpt x
        _ = Real.exp (l * Y ω) * psi l *
              (∑ x : κ, (Y ω - supProcErase g x ω)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ ≤ Real.exp (l * Y ω) * psi l * Y ω :=
            mul_le_mul_of_nonneg_left
              (sum_supProc_sub_supProcErase_le hg0 ω)
              (mul_nonneg (Real.exp_pos _).le (psi_nonneg l))
        _ = Real.exp (l * Y ω) * (Y ω * psi l) := by ring
    have hmaster2 : l * Gd l - F l * Real.log (F l) ≤ psi l * Gd l := by
      have hEq : Ex (p : ℝ) (fun ω => Real.exp (l * Y ω) * (Y ω * psi l)) =
          psi l * Gd l := by
        rw [hGd, ← Ex_smul]
        exact Ex_congr fun ω => by ring
      have hEq2 : Ex (p : ℝ) (fun ω => Y ω * Real.exp (l * Y ω)) = Gd l := rfl
      calc l * Gd l - F l * Real.log (F l)
          ≤ ∑ x : κ, Ex (p : ℝ)
              (fun ω => Real.exp (l * Y ω) * psi (l * (Y ω - supProcErase g x ω))) := by
            exact master
        _ ≤ psi l * Gd l := by rw [← hEq]; exact hsum_le
    unfold psi at hmaster2
    nlinarith [hmaster2]
  -- ODE comparison.  u := log ∘ F;  q := u / (e^· − 1) is antitone on (0,∞).
  set u : ℝ → ℝ := fun l => Real.log (F l) with hu
  have hu0 : u 0 = 0 := by rw [hu]; simp [hF0]
  have huderiv : ∀ l, HasDerivAt u (Gd l / F l) l := by
    intro l
    have := (hFderiv l).log (ne_of_gt (hFpos l))
    exact this
  rcases eq_or_lt_of_le hlam with heq | hpos
  · -- lam = 0 : both sides vanish.
    rw [← heq]
    have hL : Real.log (Ex (p : ℝ) (fun ω => Real.exp ((0:ℝ) * supProc g ω))) = 0 := by
      have h1 : (fun ω : κ → Bool => Real.exp ((0:ℝ) * supProc g ω)) =
          (fun _ : κ → Bool => (1:ℝ)) := by
        funext ω; simp
      rw [h1, Ex_const h0p h1p, Real.log_one]
    rw [hL]
    simp
  · -- main case lam > 0
    set q : ℝ → ℝ := fun l => u l / (Real.exp l - 1) with hq
    have hden : ∀ l : ℝ, 0 < l → 0 < Real.exp l - 1 := by
      intro l hl
      have := Real.exp_lt_exp.mpr hl
      simp only [Real.exp_zero] at this
      linarith [this]
    have hqderiv : ∀ l : ℝ, 0 < l → HasDerivAt q
        ((Gd l / F l * (Real.exp l - 1) - u l * Real.exp l) / (Real.exp l - 1)^2) l := by
      intro l hl
      exact (huderiv l).div ((Real.hasDerivAt_exp l).sub_const 1) (ne_of_gt (hden l hl))
    have hqanti : AntitoneOn q (Set.Ioi (0:ℝ)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      · intro l hl
        exact ((hqderiv l hl).continuousAt).continuousWithinAt
      · intro l hl
        rw [interior_Ioi] at hl
        exact (hqderiv l hl).differentiableAt.differentiableWithinAt
      · intro l hl
        rw [interior_Ioi] at hl
        rw [(hqderiv l hl).deriv]
        apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
        -- numerator ≤ 0 ⟸ (1 − e^{−l})·Gd ≤ F·log F   (multiply by e^l/F > 0)
        have hDIl := hDI l (le_of_lt hl)
        have hFl := hFpos l
        have hel : (0:ℝ) < Real.exp l := Real.exp_pos l
        have hkey : Gd l / F l * (Real.exp l - 1) ≤ u l * Real.exp l := by
          rw [hu]
          rw [div_mul_eq_mul_div, div_le_iff₀ hFl]
          have expand : (1 - Real.exp (-l)) * Real.exp l = Real.exp l - 1 := by
            rw [mul_comm, mul_sub, ← Real.exp_add]
            simp
          calc Gd l * (Real.exp l - 1) = (1 - Real.exp (-l)) * Gd l * Real.exp l := by
                rw [mul_comm (1 - Real.exp (-l)) (Gd l), mul_assoc, expand]
            _ ≤ F l * Real.log (F l) * Real.exp l := by
                apply mul_le_mul_of_nonneg_right hDIl hel.le
            _ = Real.log (F l) * Real.exp l * F l := by ring
        linarith [hkey]
    -- endpoint: q(a) → EY as a → 0⁺.
    have hslope : Filter.Tendsto (fun a => u a / a) (nhdsWithin 0 (Set.Ioi 0)) (nhds EY) := by
      have h1 := (huderiv 0).tendsto_slope
      have hval : Gd 0 / F 0 = EY := by
        rw [hF0, div_one, hGd, hEY]
        exact Ex_congr fun ω => by simp
      rw [hval] at h1
      have : (fun a => u a / a) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] slope u 0 := by
        refine Filter.eventually_of_mem self_mem_nhdsWithin fun a ha => ?_
        rw [slope_def_field, hu0, sub_zero, sub_zero]
      exact Filter.Tendsto.congr' this.symm
        (h1.mono_left (nhdsWithin_mono 0 fun a ha => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact ne_of_gt ha))
    -- (e^a − 1)/a → 1 as a → 0⁺
    have hexp_slope : Filter.Tendsto (fun a : ℝ => (Real.exp a - 1) / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have h1 := (Real.hasDerivAt_exp 0).tendsto_slope
      simp only [Real.exp_zero] at h1
      have : (fun a : ℝ => (Real.exp a - 1) / a) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          slope Real.exp 0 := by
        refine Filter.eventually_of_mem self_mem_nhdsWithin fun a ha => ?_
        rw [slope_def_field, Real.exp_zero, sub_zero]
      exact Filter.Tendsto.congr' this.symm
        (h1.mono_left (nhdsWithin_mono 0 fun a ha => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact ne_of_gt ha))
    -- q a → EY as a → 0⁺
    have hqtend : Filter.Tendsto q (nhdsWithin 0 (Set.Ioi 0)) (nhds EY) := by
      have hdiv := Filter.Tendsto.div hslope hexp_slope one_ne_zero
      simp only [div_one] at hdiv
      have : q =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun a => (u a / a) / ((Real.exp a - 1) / a)) := by
        refine Filter.eventually_of_mem self_mem_nhdsWithin fun a ha => ?_
        have ha0 : (a:ℝ) ≠ 0 := ne_of_gt ha
        have hea : Real.exp a - 1 ≠ 0 := ne_of_gt (hden a ha)
        rw [hq]
        field_simp
      exact Filter.Tendsto.congr' this.symm hdiv
    -- q lam ≤ q a eventually, hence q lam ≤ EY.
    have hqle : ∀ᶠ a in nhdsWithin 0 (Set.Ioi 0), q lam ≤ q a := by
      have hmem : Set.Ioo (0:ℝ) lam ∈ nhdsWithin 0 (Set.Ioi 0) := by
        apply mem_nhdsWithin.mpr
        exact ⟨Set.Iio lam, isOpen_Iio, hpos, fun a ⟨ha1, ha2⟩ => ⟨ha2, ha1⟩⟩
      filter_upwards [hmem] with a ha
      exact hqanti (Set.mem_Ioi.mpr ha.1) (Set.mem_Ioi.mpr hpos) (le_of_lt ha.2)
    have hfinal : q lam ≤ EY := ge_of_tendsto hqtend hqle
    -- unfold q and multiply through.
    have hden_lam : 0 < Real.exp lam - 1 := hden lam hpos
    rw [hq] at hfinal
    have := (div_le_iff₀ hden_lam).mp hfinal
    calc Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * supProc g ω))) = u lam := rfl
      _ ≤ EY * (Real.exp lam - 1) := this
      _ = Ex (p : ℝ) (fun ω => supProc g ω) * (Real.exp lam - 1) := by rw [hEY]

/-- Laplace form of T1. -/
theorem selfbounding_exp_bound (p : NNReal) (hp : p ≤ 1)
    (g : ι → κ → Bool → ℝ) (hg0 : ∀ a x b, 0 ≤ g a x b) (hg1 : ∀ a x b, g a x b ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Ex (p : ℝ) (fun ω => Real.exp (lam * supProc g ω)) ≤
      Real.exp (Ex (p : ℝ) (fun ω => supProc g ω) * (Real.exp lam - 1)) := by
  have h := selfbounding_mgf_bound p hp g hg0 hg1 lam hlam
  have hFpos : 0 < Ex (p : ℝ) (fun ω => Real.exp (lam * supProc g ω)) :=
    Ex_pos p.coe_nonneg (by exact_mod_cast hp) (fun ω => Real.exp_pos _)
  calc Ex (p : ℝ) (fun ω => Real.exp (lam * supProc g ω))
      = Real.exp (Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * supProc g ω)))) :=
        (Real.exp_log hFpos).symm
    _ ≤ Real.exp (Ex (p : ℝ) (fun ω => supProc g ω) * (Real.exp lam - 1)) :=
        Real.exp_le_exp.mpr h

end TalagrandCore
end

/-! ## Component: TwoCopy -/
section
/-
Block T2: the two-copy entropy differential inequality for the linear process
supremum, valid for both `V = Z` and `V = −Z` (Ledoux (2.7) with the swap
symmetry handling the second argmax).

For `|c_a(x)| ≤ 1`, `∑_x p(1−p) c_a(x)² ≤ σ²`, `lam ≥ 0`, and `V ∈ {Z, −Z}`:

  Ent(e^{lam V}) ≤ lam² e^{2 lam} · Ex[e^{lam V}·(Σ² + σ²)].
-/

open scoped BigOperators

namespace TalagrandCore

/-- Second-order bound on the decaying side: `e^{-u} - 1 + u ≤ u²/2` for `u ≥ 0`. -/
private theorem psi_le_half_sq (u : ℝ) (hu : 0 ≤ u) : psi u ≤ u ^ 2 / 2 := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun x => x ^ 2 / 2 + 1 - x - Real.exp (-x))
    (f' := fun x => x - 1 + Real.exp (-x))
    (fun x _ => by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
        exact ((hasDerivAt_neg' x).exp).congr_deriv (by ring)
      have := (((hsq.div_const 2).add_const 1).sub (hasDerivAt_id x)).sub hexp
      exact this.congr_deriv (by ring))
    (by norm_num)
    (fun x _ => by
      have := psi_nonneg x
      unfold psi at this
      linarith)
    u hu
  unfold psi
  linarith [key]

/-- Taylor-type bound on the growing side: `e^v - 1 - v ≤ (v²/2)·e^v` for `v ≥ 0`. -/
private theorem exp_sub_one_sub_le (v : ℝ) (hv : 0 ≤ v) :
    Real.exp v - 1 - v ≤ v ^ 2 / 2 * Real.exp v := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun x => x ^ 2 / 2 - 1 + Real.exp (-x) + x * Real.exp (-x))
    (f' := fun x => x - x * Real.exp (-x))
    (fun x _ => by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
        exact ((hasDerivAt_neg' x).exp).congr_deriv (by ring)
      have hmul : HasDerivAt (fun y : ℝ => y * Real.exp (-y))
          (1 * Real.exp (-x) + x * (-Real.exp (-x))) x :=
        (hasDerivAt_id x).mul hexp
      have := (((hsq.div_const 2).sub_const 1).add hexp).add hmul
      exact this.congr_deriv (by ring))
    (by norm_num)
    (fun x hx => by
      have hle : Real.exp (-x) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      nlinarith)
    v hv
  have hid : Real.exp v * Real.exp (-v) = 1 := by
    rw [← Real.exp_add]; simp
  have hid2 : v * (Real.exp v * Real.exp (-v)) = v := by rw [hid, mul_one]
  nlinarith [mul_nonneg key (Real.exp_pos v).le]

/-- ψ-kernel elementary bound: `ψ(u) ≤ (u²/2)·e^{|u|}` (used with `|u| ≤ lam`). -/
theorem psi_le_sq_exp (u : ℝ) : psi u ≤ u ^ 2 / 2 * Real.exp |u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    have h1 := psi_le_half_sq u hu
    have h2 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
    nlinarith [sq_nonneg u]
  · rw [abs_of_neg hu]
    have h := exp_sub_one_sub_le (-u) (by linarith)
    unfold psi
    have hsq : (-u) ^ 2 = u ^ 2 := by ring
    rw [hsq] at h
    linarith

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-- The `bw`-weighted pair of expectations as a single sum over `(ω, t)` pairs. -/
private theorem pair_sum_eq (q : ℝ) (g : (κ → Bool) → Bool → ℝ) :
    bw q true * Ex q (fun ω => g ω true) + bw q false * Ex q (fun ω => g ω false) =
      ∑ ωt : (κ → Bool) × Bool, W q ωt.1 * bw q ωt.2 * g ωt.1 ωt.2 := by
  unfold Ex
  rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [Fintype.sum_bool]
  ring

/-- Swap symmetry of the `(ω, t)`-pair measure under `(ω, t) ↦ (update ω x t, ω x)`. -/
private theorem Ex_swap_pair (q : ℝ) (x : κ) (f : (κ → Bool) → Bool → ℝ) :
    bw q true * Ex q (fun ω => f ω true) + bw q false * Ex q (fun ω => f ω false) =
      bw q true * Ex q (fun ω => f (Function.update ω x true) (ω x)) +
        bw q false * Ex q (fun ω => f (Function.update ω x false) (ω x)) := by
  have key : ∑ ωt : (κ → Bool) × Bool, W q ωt.1 * bw q ωt.2 * f ωt.1 ωt.2 =
      ∑ ωt : (κ → Bool) × Bool,
        W q ωt.1 * bw q ωt.2 * f (Function.update ωt.1 x ωt.2) (ωt.1 x) := by
    refine Finset.sum_nbij'
      (i := fun ωt : (κ → Bool) × Bool => (Function.update ωt.1 x ωt.2, ωt.1 x))
      (j := fun ωt : (κ → Bool) × Bool => (Function.update ωt.1 x ωt.2, ωt.1 x))
      ?_ ?_ ?_ ?_ ?_
    · intro ωt _; exact Finset.mem_univ _
    · intro ωt _; exact Finset.mem_univ _
    · intro ωt _
      obtain ⟨ω, t⟩ := ωt
      simp [Function.update_idem, Function.update_eq_self]
    · intro ωt _
      obtain ⟨ω, t⟩ := ωt
      simp [Function.update_idem, Function.update_eq_self]
    · intro ωt _
      obtain ⟨ω, t⟩ := ωt
      simp only
      have e1 : Function.update (Function.update ω x t) x (ω x) = ω := by
        rw [Function.update_idem]; exact Function.update_eq_self x ω
      have e2 : Function.update ω x t x = t := by simp
      rw [e1, e2, W_eq_bw_mul_Wrest x ω,
        W_eq_bw_mul_Wrest (p := q) x (Function.update ω x t), Wrest_update, e2]
      ring
  calc bw q true * Ex q (fun ω => f ω true) + bw q false * Ex q (fun ω => f ω false)
      = ∑ ωt : (κ → Bool) × Bool, W q ωt.1 * bw q ωt.2 * f ωt.1 ωt.2 :=
        pair_sum_eq q f
    _ = ∑ ωt : (κ → Bool) × Bool,
          W q ωt.1 * bw q ωt.2 * f (Function.update ωt.1 x ωt.2) (ωt.1 x) := key
    _ = _ := (pair_sum_eq q (fun ω t => f (Function.update ω x t) (ω x))).symm

/-- A choice of argmax for `Zproc` at each configuration. -/
private noncomputable def argmaxZ (coeff : ι → κ → ℝ) (q : ℝ) (ω : κ → Bool) : ι :=
  Classical.choose (supProc_exists_argmax (linSummand coeff q) ω)

private theorem argmaxZ_spec (coeff : ι → κ → ℝ) (q : ℝ) (ω : κ → Bool) :
    Zproc coeff q ω = ∑ y : κ, (cond (ω y) (1:ℝ) 0 - q) * coeff (argmaxZ coeff q ω) y := by
  have h := Classical.choose_spec (supProc_exists_argmax (linSummand coeff q) ω)
  simpa [Zproc, linSummand, argmaxZ] using h

/-- Upper one-sided Lipschitz bound via the argmax at `ω`. -/
private theorem Zdiff_le (coeff : ι → κ → ℝ) (q : ℝ) (ω : κ → Bool) (x : κ) (t : Bool) :
    Zproc coeff q ω - Zproc coeff q (Function.update ω x t) ≤
      (cond (ω x) (1:ℝ) 0 - cond t 1 0) * coeff (argmaxZ coeff q ω) x :=
  Zproc_update_le coeff q ω x t _ (argmaxZ_spec coeff q ω)

/-- Lower one-sided Lipschitz bound via the argmax at `update ω x t`. -/
private theorem Zdiff_ge (coeff : ι → κ → ℝ) (q : ℝ) (ω : κ → Bool) (x : κ) (t : Bool) :
    Zproc coeff q (Function.update ω x t) - Zproc coeff q ω ≤
      (cond t (1:ℝ) 0 - cond (ω x) 1 0) *
        coeff (argmaxZ coeff q (Function.update ω x t)) x := by
  have h := Zproc_update_le coeff q (Function.update ω x t) x (ω x) _
    (argmaxZ_spec coeff q (Function.update ω x t))
  have e1 : Function.update (Function.update ω x t) x (ω x) = ω := by
    rw [Function.update_idem]; exact Function.update_eq_self x ω
  have e2 : Function.update ω x t x = t := by simp
  rw [e1, e2] at h
  exact h

/-- Refined two-argmax square bound. -/
private theorem Zdiff_sq_le (coeff : ι → κ → ℝ) (q : ℝ) (ω : κ → Bool) (x : κ) (t : Bool) :
    (Zproc coeff q ω - Zproc coeff q (Function.update ω x t)) ^ 2 ≤
      (cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 *
        (coeff (argmaxZ coeff q ω) x ^ 2 +
          coeff (argmaxZ coeff q (Function.update ω x t)) x ^ 2) := by
  set D := Zproc coeff q ω - Zproc coeff q (Function.update ω x t) with hD
  set s := cond (ω x) (1:ℝ) 0 - cond t 1 0 with hs
  set c1 := coeff (argmaxZ coeff q ω) x with hc1
  set c2 := coeff (argmaxZ coeff q (Function.update ω x t)) x with hc2
  have h1 : D ≤ s * c1 := Zdiff_le coeff q ω x t
  have h2 : s * c2 ≤ D := by
    have h := Zdiff_ge coeff q ω x t
    rw [hD, hs, hc2]
    linarith [h]
  rcases le_or_gt 0 D with hD0 | hD0
  · have hsq : D ^ 2 ≤ (s * c1) ^ 2 := by nlinarith [mul_self_le_mul_self hD0 h1]
    nlinarith [sq_nonneg (s * c2)]
  · have hsq : D ^ 2 ≤ (s * c2) ^ 2 := by nlinarith [h2, hD0]
    nlinarith [sq_nonneg (s * c1)]

/-- Coarse one-coordinate bound: `|Z ω − Z (update ω x t)| ≤ 1` when `|coeff| ≤ 1`. -/
private theorem Zdiff_abs_le (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (q : ℝ) (ω : κ → Bool) (x : κ) (t : Bool) :
    |Zproc coeff q ω - Zproc coeff q (Function.update ω x t)| ≤ 1 := by
  have h1 := Zdiff_le coeff q ω x t
  have h2 := Zdiff_ge coeff q ω x t
  have hs : |cond (ω x) (1:ℝ) 0 - cond t 1 0| ≤ 1 := by
    cases ω x <;> cases t <;> norm_num
  have hb1 := hB (argmaxZ coeff q ω) x
  have hb2 := hB (argmaxZ coeff q (Function.update ω x t)) x
  rw [abs_le]
  constructor
  · have : (cond t (1:ℝ) 0 - cond (ω x) 1 0) *
        coeff (argmaxZ coeff q (Function.update ω x t)) x ≤ 1 := by
      calc (cond t (1:ℝ) 0 - cond (ω x) 1 0) *
            coeff (argmaxZ coeff q (Function.update ω x t)) x
          ≤ |(cond t (1:ℝ) 0 - cond (ω x) 1 0) *
              coeff (argmaxZ coeff q (Function.update ω x t)) x| := le_abs_self _
        _ = |cond t (1:ℝ) 0 - cond (ω x) 1 0| *
              |coeff (argmaxZ coeff q (Function.update ω x t)) x| := abs_mul _ _
        _ ≤ 1 * 1 := by
            apply mul_le_mul _ hb2 (abs_nonneg _) zero_le_one
            calc |cond t (1:ℝ) 0 - cond (ω x) 1 0|
                = |cond (ω x) (1:ℝ) 0 - cond t 1 0| := by rw [abs_sub_comm]
              _ ≤ 1 := hs
        _ = 1 := one_mul 1
    linarith
  · have : (cond (ω x) (1:ℝ) 0 - cond t 1 0) * coeff (argmaxZ coeff q ω) x ≤ 1 := by
      calc (cond (ω x) (1:ℝ) 0 - cond t 1 0) * coeff (argmaxZ coeff q ω) x
          ≤ |(cond (ω x) (1:ℝ) 0 - cond t 1 0) * coeff (argmaxZ coeff q ω) x| :=
            le_abs_self _
        _ = |cond (ω x) (1:ℝ) 0 - cond t 1 0| * |coeff (argmaxZ coeff q ω) x| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul hs hb1 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    linarith

/-- Kernel bound: `ψ(lam·D) ≤ (lam²/2)·e^{lam}·D²` for `|D| ≤ 1`, `lam ≥ 0`. -/
private theorem kernel_bound (lam D : ℝ) (hlam : 0 ≤ lam) (hD : |D| ≤ 1) :
    psi (lam * D) ≤ lam ^ 2 / 2 * Real.exp lam * D ^ 2 := by
  have h1 := psi_le_sq_exp (lam * D)
  have h2 : |lam * D| ≤ lam := by
    rw [abs_mul, abs_of_nonneg hlam]
    nlinarith [abs_nonneg D]
  have h3 : Real.exp |lam * D| ≤ Real.exp lam := Real.exp_le_exp.mpr h2
  calc psi (lam * D) ≤ (lam * D) ^ 2 / 2 * Real.exp |lam * D| := h1
    _ ≤ (lam * D) ^ 2 / 2 * Real.exp lam := by
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = lam ^ 2 / 2 * Real.exp lam * D ^ 2 := by ring

/-- Two-point average identity: `bwT·(χb−1)² + bwF·(χb−0)² = (χb−q)² + q(1−q)`. -/
private theorem two_point_avg (q : ℝ) (b : Bool) :
    bw q true * (cond b (1:ℝ) 0 - cond true (1:ℝ) 0) ^ 2 +
      bw q false * (cond b (1:ℝ) 0 - cond false (1:ℝ) 0) ^ 2 =
    (cond b (1:ℝ) 0 - q) ^ 2 + q * (1 - q) := by
  cases b <;> simp [bw] <;> ring

omit [DecidableEq κ] in
/-- Summed variance bound at the argmax: dominated by `Σ² + σ²`. -/
private theorem sigma_sum_le (coeff : ι → κ → ℝ) (q : ℝ) (sigmaSq : ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, q * (1 - q) * coeff a x ^ 2 ≤ sigmaSq)
    (a : ι) (ω : κ → Bool) :
    ∑ x : κ, coeff a x ^ 2 * ((cond (ω x) (1:ℝ) 0 - q) ^ 2 + q * (1 - q)) ≤
      Sigma2 coeff q ω + sigmaSq := by
  have hsplit : ∑ x : κ, coeff a x ^ 2 * ((cond (ω x) (1:ℝ) 0 - q) ^ 2 + q * (1 - q)) =
      (∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - q) ^ 2) +
        ∑ x : κ, q * (1 - q) * coeff a x ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsplit]
  have h1 : (∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - q) ^ 2) ≤
      Sigma2 coeff q ω := by
    unfold Sigma2
    exact Finset.le_sup'
      (f := fun a : ι => ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - q) ^ 2)
      (Finset.mem_univ a)
  linarith [hVar a]

omit [DecidableEq κ] in
/-- `Sigma2` is nonnegative. -/
private theorem Sigma2_nonneg' (coeff : ι → κ → ℝ) (q : ℝ) (ω : κ → Bool) :
    0 ≤ Sigma2 coeff q ω := by
  obtain ⟨a⟩ := (inferInstance : Nonempty ι)
  have h1 : (0:ℝ) ≤ ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - q) ^ 2 :=
    Finset.sum_nonneg fun x _ => by positivity
  refine le_trans h1 ?_
  unfold Sigma2
  exact Finset.le_sup'
    (f := fun a : ι => ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - q) ^ 2)
    (Finset.mem_univ a)

/-- Pointwise weighted form of `two_point_avg`. -/
private theorem two_point_avg_mul (q : ℝ) (b : Bool) (g w : ℝ) :
    bw q true * (g * ((cond b (1:ℝ) 0 - cond true (1:ℝ) 0) ^ 2 * w)) +
      bw q false * (g * ((cond b (1:ℝ) 0 - cond false (1:ℝ) 0) ^ 2 * w)) =
      g * (w * ((cond b (1:ℝ) 0 - q) ^ 2 + q * (1 - q))) := by
  have h := two_point_avg q b
  linear_combination g * w * h

/-- Abstract real-number assembly of the per-coordinate bounds. -/
private theorem combine_bounds {bT bF ET EF PT PF QT QF RT RF M C el : ℝ}
    (hbT : 0 ≤ bT) (hbF : 0 ≤ bF) (hC : 0 ≤ C)
    (h1T : ET ≤ C * (PT + QT)) (h1F : EF ≤ C * (PF + QF))
    (h3T : QT ≤ el * RT) (h3F : QF ≤ el * RF)
    (hswap : bT * PT + bF * PF = bT * RT + bF * RF)
    (hM : bT * PT + bF * PF = M) :
    bT * ET + bF * EF ≤ C * (1 + el) * M := by
  calc bT * ET + bF * EF
      ≤ bT * (C * (PT + QT)) + bF * (C * (PF + QF)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1T hbT)
          (mul_le_mul_of_nonneg_left h1F hbF)
    _ = C * ((bT * PT + bF * PF) + (bT * QT + bF * QF)) := by ring
    _ ≤ C * ((bT * PT + bF * PF) + (bT * (el * RT) + bF * (el * RF))) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have hqt := mul_le_mul_of_nonneg_left h3T hbT
        have hqf := mul_le_mul_of_nonneg_left h3F hbF
        linarith
    _ = C * ((bT * PT + bF * PF) + el * (bT * RT + bF * RF)) := by ring
    _ = C * ((bT * PT + bF * PF) + el * (bT * PT + bF * PF)) := by rw [← hswap]
    _ = C * (1 + el) * (bT * PT + bF * PF) := by ring
    _ = C * (1 + el) * M := by rw [hM]

/-- Per-coordinate two-copy bound: the `bw`-average over the two `c`-families of
the ψ-terms at coordinate `x` is controlled by the local variance term. -/
private theorem per_coord_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (V u : (κ → Bool) → ℝ) (x : κ)
    (hu : ∀ ω, 0 ≤ u ω)
    (hD1 : ∀ ω t, |V ω - V (Function.update ω x t)| ≤ 1)
    (hDsq : ∀ ω t, (V ω - V (Function.update ω x t)) ^ 2 ≤
        (cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 * (u ω + u (Function.update ω x t))) :
    bw q true * Ex q (fun ω => Real.exp (lam * V ω) *
        psi (lam * (V ω - V (Function.update ω x true)))) +
      bw q false * Ex q (fun ω => Real.exp (lam * V ω) *
        psi (lam * (V ω - V (Function.update ω x false)))) ≤
      lam ^ 2 / 2 * Real.exp lam * (1 + Real.exp lam) *
        Ex q (fun ω => Real.exp (lam * V ω) *
          (u ω * ((cond (ω x) (1:ℝ) 0 - q) ^ 2 + q * (1 - q)))) := by
  have hbwT := bw_nonneg hq0 hq1 true
  have hbwF := bw_nonneg hq0 hq1 false
  have step1 : ∀ t : Bool,
      Ex q (fun ω => Real.exp (lam * V ω) *
          psi (lam * (V ω - V (Function.update ω x t)))) ≤
        lam ^ 2 / 2 * Real.exp lam *
          (Ex q (fun ω => Real.exp (lam * V ω) *
              ((cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 * u ω)) +
            Ex q (fun ω => Real.exp (lam * V ω) *
              ((cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 * u (Function.update ω x t)))) := by
    intro t
    rw [← Ex_add, ← Ex_smul]
    apply Ex_mono hq0 hq1
    intro ω
    have hk := kernel_bound lam (V ω - V (Function.update ω x t)) hlam (hD1 ω t)
    have hs := hDsq ω t
    have hexp : (0:ℝ) ≤ Real.exp (lam * V ω) := (Real.exp_pos _).le
    calc Real.exp (lam * V ω) * psi (lam * (V ω - V (Function.update ω x t)))
        ≤ Real.exp (lam * V ω) * (lam ^ 2 / 2 * Real.exp lam *
            (V ω - V (Function.update ω x t)) ^ 2) :=
          mul_le_mul_of_nonneg_left hk hexp
      _ ≤ Real.exp (lam * V ω) * (lam ^ 2 / 2 * Real.exp lam *
            ((cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 *
              (u ω + u (Function.update ω x t)))) := by
          apply mul_le_mul_of_nonneg_left _ hexp
          exact mul_le_mul_of_nonneg_left hs (by positivity)
      _ = lam ^ 2 / 2 * Real.exp lam *
            (Real.exp (lam * V ω) *
                ((cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 * u ω) +
              Real.exp (lam * V ω) *
                ((cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 *
                  u (Function.update ω x t))) := by ring
  have step3 : ∀ t : Bool,
      Ex q (fun ω => Real.exp (lam * V ω) *
          ((cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 * u (Function.update ω x t))) ≤
        Real.exp lam * Ex q (fun ω => Real.exp (lam * V (Function.update ω x t)) *
          ((cond (Function.update ω x t x) (1:ℝ) 0 - cond (ω x) 1 0) ^ 2 *
            u (Function.update ω x t))) := by
    intro t
    rw [← Ex_smul]
    apply Ex_mono hq0 hq1
    intro ω
    have hGle : Real.exp (lam * V ω) ≤
        Real.exp lam * Real.exp (lam * V (Function.update ω x t)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := (abs_le.mp (hD1 ω t)).2
      linarith [mul_le_mul_of_nonneg_left h hlam]
    have e2 : Function.update ω x t x = t := by simp
    have hseq : (cond (Function.update ω x t x) (1:ℝ) 0 - cond (ω x) 1 0) ^ 2 =
        (cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 := by rw [e2]; ring
    calc Real.exp (lam * V ω) *
          ((cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 * u (Function.update ω x t))
        ≤ (Real.exp lam * Real.exp (lam * V (Function.update ω x t))) *
            ((cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 * u (Function.update ω x t)) :=
          mul_le_mul_of_nonneg_right hGle
            (mul_nonneg (sq_nonneg _) (hu _))
      _ = Real.exp lam * (Real.exp (lam * V (Function.update ω x t)) *
            ((cond (Function.update ω x t x) (1:ℝ) 0 - cond (ω x) 1 0) ^ 2 *
              u (Function.update ω x t))) := by rw [hseq]; ring
  have hswap :
      bw q true * Ex q (fun ω => Real.exp (lam * V ω) *
          ((cond (ω x) (1:ℝ) 0 - cond true (1:ℝ) 0) ^ 2 * u ω)) +
        bw q false * Ex q (fun ω => Real.exp (lam * V ω) *
          ((cond (ω x) (1:ℝ) 0 - cond false (1:ℝ) 0) ^ 2 * u ω)) =
      bw q true * Ex q (fun ω => Real.exp (lam * V (Function.update ω x true)) *
          ((cond (Function.update ω x true x) (1:ℝ) 0 - cond (ω x) 1 0) ^ 2 *
            u (Function.update ω x true))) +
        bw q false * Ex q (fun ω => Real.exp (lam * V (Function.update ω x false)) *
          ((cond (Function.update ω x false x) (1:ℝ) 0 - cond (ω x) 1 0) ^ 2 *
            u (Function.update ω x false))) :=
    Ex_swap_pair q x (fun ω t => Real.exp (lam * V ω) *
      ((cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 * u ω))
  have hM :
      bw q true * Ex q (fun ω => Real.exp (lam * V ω) *
          ((cond (ω x) (1:ℝ) 0 - cond true (1:ℝ) 0) ^ 2 * u ω)) +
        bw q false * Ex q (fun ω => Real.exp (lam * V ω) *
          ((cond (ω x) (1:ℝ) 0 - cond false (1:ℝ) 0) ^ 2 * u ω)) =
      Ex q (fun ω => Real.exp (lam * V ω) *
        (u ω * ((cond (ω x) (1:ℝ) 0 - q) ^ 2 + q * (1 - q)))) := by
    rw [← Ex_smul, ← Ex_smul, ← Ex_add]
    exact Ex_congr fun ω => two_point_avg_mul q (ω x) (Real.exp (lam * V ω)) (u ω)
  exact combine_bounds hbwT hbwF (by positivity)
    (step1 true) (step1 false) (step3 true) (step3 false) hswap hM

/-- Final constant absorption: `(lam²/2)·e^{lam}·(1+e^{lam}) ≤ lam²·e^{2lam}`. -/
private theorem const_absorb (lam : ℝ) (hlam : 0 ≤ lam) :
    lam ^ 2 / 2 * Real.exp lam * (1 + Real.exp lam) ≤ lam ^ 2 * Real.exp (2 * lam) := by
  have h1 : (1:ℝ) ≤ Real.exp lam := Real.one_le_exp hlam
  have h2 : Real.exp (2 * lam) = Real.exp lam * Real.exp lam := by
    rw [← Real.exp_add, two_mul]
  rw [h2]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg lam) (Real.exp_pos lam).le)
    (by linarith : (0:ℝ) ≤ Real.exp lam - 1)]

/-- Convex combination of two upper bounds. -/
private theorem convex_combine {E ST SF b1 b2 : ℝ} (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hsum : b1 + b2 = 1) (h1 : E ≤ ST) (h2 : E ≤ SF) :
    E ≤ b1 * ST + b2 * SF := by
  calc E = (b1 + b2) * E := by rw [hsum, one_mul]
    _ = b1 * E + b2 * E := by ring
    _ ≤ b1 * ST + b2 * SF :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hb1) (mul_le_mul_of_nonneg_left h2 hb2)

/-- Generic two-copy entropy bound: works for any `V` with the two-argmax
Lipschitz structure relative to the `Zproc` argmax (covers `V = Z` and `V = −Z`). -/
private theorem two_copy_core (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (sigmaSq : ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (V : (κ → Bool) → ℝ)
    (hD1 : ∀ (ω : κ → Bool) (x : κ) (t : Bool),
      |V ω - V (Function.update ω x t)| ≤ 1)
    (hDsq : ∀ (ω : κ → Bool) (x : κ) (t : Bool),
      (V ω - V (Function.update ω x t)) ^ 2 ≤
        (cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 *
          (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 +
            coeff (argmaxZ coeff (p : ℝ) (Function.update ω x t)) x ^ 2)) :
    lam * Ex (p : ℝ) (fun ω => V ω * Real.exp (lam * V ω)) -
      Ex (p : ℝ) (fun ω => Real.exp (lam * V ω)) *
        Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * V ω))) ≤
      lam ^ 2 * Real.exp (2 * lam) *
        Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
          (Sigma2 coeff (p : ℝ) ω + sigmaSq)) := by
  have hq0 : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have hq1 : ((p : ℝ)) ≤ 1 := by exact_mod_cast hp
  have hbwT := bw_nonneg hq0 hq1 true
  have hbwF := bw_nonneg hq0 hq1 false
  have hb := bw_sum (p : ℝ)
  have hsig : (0:ℝ) ≤ sigmaSq := by
    obtain ⟨a⟩ := (inferInstance : Nonempty ι)
    refine le_trans ?_ (hVar a)
    apply Finset.sum_nonneg
    intro x _
    have h1 : (0:ℝ) ≤ (p : ℝ) * (1 - (p : ℝ)) := mul_nonneg hq0 (by linarith)
    exact mul_nonneg h1 (sq_nonneg _)
  have hct : ∀ (t : Bool) (x : κ), FiberConst x (fun ω => V (Function.update ω x t)) := by
    intro t x ω s
    show V (Function.update (Function.update ω x s) x t) = V (Function.update ω x t)
    rw [Function.update_idem]
  have master : ∀ t : Bool,
      lam * Ex (p : ℝ) (fun ω => V ω * Real.exp (lam * V ω)) -
        Ex (p : ℝ) (fun ω => Real.exp (lam * V ω)) *
          Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * V ω))) ≤
        ∑ x : κ, Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
          psi (lam * (V ω - V (Function.update ω x t)))) :=
    fun t => entropy_tensor_psi p hp V lam
      (fun x ω => V (Function.update ω x t)) (hct t)
  have hx : ∀ x : κ,
      bw (p : ℝ) true * Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
          psi (lam * (V ω - V (Function.update ω x true)))) +
        bw (p : ℝ) false * Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
          psi (lam * (V ω - V (Function.update ω x false)))) ≤
        lam ^ 2 / 2 * Real.exp lam * (1 + Real.exp lam) *
          Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
            (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 *
              ((cond (ω x) (1:ℝ) 0 - (p : ℝ)) ^ 2 + (p : ℝ) * (1 - (p : ℝ))))) :=
    fun x => per_coord_bound (p : ℝ) hq0 hq1 lam hlam V
      (fun ω => coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2) x
      (fun ω => sq_nonneg _) (fun ω t => hD1 ω x t) (fun ω t => hDsq ω x t)
  have hfin : Ex (p : ℝ) (fun ω => ∑ x : κ, Real.exp (lam * V ω) *
        (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 *
          ((cond (ω x) (1:ℝ) 0 - (p : ℝ)) ^ 2 + (p : ℝ) * (1 - (p : ℝ))))) =
      ∑ x : κ, Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
        (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 *
          ((cond (ω x) (1:ℝ) 0 - (p : ℝ)) ^ 2 + (p : ℝ) * (1 - (p : ℝ))))) :=
    Ex_finsum Finset.univ (fun x ω => Real.exp (lam * V ω) *
      (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 *
        ((cond (ω x) (1:ℝ) 0 - (p : ℝ)) ^ 2 + (p : ℝ) * (1 - (p : ℝ)))))
  calc lam * Ex (p : ℝ) (fun ω => V ω * Real.exp (lam * V ω)) -
        Ex (p : ℝ) (fun ω => Real.exp (lam * V ω)) *
          Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * V ω)))
      ≤ bw (p : ℝ) true * (∑ x : κ, Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
            psi (lam * (V ω - V (Function.update ω x true))))) +
          bw (p : ℝ) false * (∑ x : κ, Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
            psi (lam * (V ω - V (Function.update ω x false))))) :=
        convex_combine hbwT hbwF hb (master true) (master false)
    _ = ∑ x : κ, (bw (p : ℝ) true * Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
            psi (lam * (V ω - V (Function.update ω x true)))) +
          bw (p : ℝ) false * Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
            psi (lam * (V ω - V (Function.update ω x false))))) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ ∑ x : κ, lam ^ 2 / 2 * Real.exp lam * (1 + Real.exp lam) *
          Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
            (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 *
              ((cond (ω x) (1:ℝ) 0 - (p : ℝ)) ^ 2 + (p : ℝ) * (1 - (p : ℝ))))) :=
        Finset.sum_le_sum fun x _ => hx x
    _ = lam ^ 2 / 2 * Real.exp lam * (1 + Real.exp lam) *
          ∑ x : κ, Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
            (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 *
              ((cond (ω x) (1:ℝ) 0 - (p : ℝ)) ^ 2 + (p : ℝ) * (1 - (p : ℝ))))) := by
        rw [← Finset.mul_sum]
    _ = lam ^ 2 / 2 * Real.exp lam * (1 + Real.exp lam) *
          Ex (p : ℝ) (fun ω => ∑ x : κ, Real.exp (lam * V ω) *
            (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 *
              ((cond (ω x) (1:ℝ) 0 - (p : ℝ)) ^ 2 + (p : ℝ) * (1 - (p : ℝ))))) := by
        rw [hfin]
    _ ≤ lam ^ 2 / 2 * Real.exp lam * (1 + Real.exp lam) *
          Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
            (Sigma2 coeff (p : ℝ) ω + sigmaSq)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Ex_mono hq0 hq1
        intro ω
        have hsum := sigma_sum_le coeff (p : ℝ) sigmaSq hVar
          (argmaxZ coeff (p : ℝ) ω) ω
        calc ∑ x : κ, Real.exp (lam * V ω) *
              (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 *
                ((cond (ω x) (1:ℝ) 0 - (p : ℝ)) ^ 2 + (p : ℝ) * (1 - (p : ℝ))))
            = Real.exp (lam * V ω) * ∑ x : κ,
                coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 *
                  ((cond (ω x) (1:ℝ) 0 - (p : ℝ)) ^ 2 + (p : ℝ) * (1 - (p : ℝ))) := by
              rw [Finset.mul_sum]
          _ ≤ Real.exp (lam * V ω) * (Sigma2 coeff (p : ℝ) ω + sigmaSq) :=
              mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ ≤ lam ^ 2 * Real.exp (2 * lam) *
          Ex (p : ℝ) (fun ω => Real.exp (lam * V ω) *
            (Sigma2 coeff (p : ℝ) ω + sigmaSq)) := by
        apply mul_le_mul_of_nonneg_right (const_absorb lam hlam)
        apply Ex_nonneg hq0 hq1
        intro ω
        have h1 := Sigma2_nonneg' coeff (p : ℝ) ω
        exact mul_nonneg (Real.exp_pos _).le (by linarith)

/-- **T2 for `V = Z`.** -/
theorem two_copy_entropy_Z (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (sigmaSq : ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    lam * Ex (p : ℝ) (fun ω => Zproc coeff (p : ℝ) ω *
        Real.exp (lam * Zproc coeff (p : ℝ) ω)) -
      Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω)) *
        Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω))) ≤
      lam ^ 2 * Real.exp (2 * lam) *
        Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω) *
          (Sigma2 coeff (p : ℝ) ω + sigmaSq)) := by
  exact two_copy_core p hp coeff sigmaSq hVar lam hlam (Zproc coeff (p : ℝ))
    (fun ω x t => Zdiff_abs_le coeff hB (p : ℝ) ω x t)
    (fun ω x t => Zdiff_sq_le coeff (p : ℝ) ω x t)

/-- **T2 for `V = −Z`.** -/
theorem two_copy_entropy_negZ (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (sigmaSq : ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    lam * Ex (p : ℝ) (fun ω => (-Zproc coeff (p : ℝ) ω) *
        Real.exp (lam * (-Zproc coeff (p : ℝ) ω))) -
      Ex (p : ℝ) (fun ω => Real.exp (lam * (-Zproc coeff (p : ℝ) ω))) *
        Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * (-Zproc coeff (p : ℝ) ω)))) ≤
      lam ^ 2 * Real.exp (2 * lam) *
        Ex (p : ℝ) (fun ω => Real.exp (lam * (-Zproc coeff (p : ℝ) ω)) *
          (Sigma2 coeff (p : ℝ) ω + sigmaSq)) := by
  exact two_copy_core p hp coeff sigmaSq hVar lam hlam
    (fun ω => -Zproc coeff (p : ℝ) ω)
    (fun ω x t => by
      show |(-Zproc coeff (p : ℝ) ω) - (-Zproc coeff (p : ℝ) (Function.update ω x t))| ≤ 1
      have h := Zdiff_abs_le coeff hB (p : ℝ) ω x t
      have e : (-Zproc coeff (p : ℝ) ω) - (-Zproc coeff (p : ℝ) (Function.update ω x t)) =
          -(Zproc coeff (p : ℝ) ω - Zproc coeff (p : ℝ) (Function.update ω x t)) := by ring
      rw [e, abs_neg]
      exact h)
    (fun ω x t => by
      show ((-Zproc coeff (p : ℝ) ω) - (-Zproc coeff (p : ℝ) (Function.update ω x t))) ^ 2 ≤
        (cond (ω x) (1:ℝ) 0 - cond t 1 0) ^ 2 *
          (coeff (argmaxZ coeff (p : ℝ) ω) x ^ 2 +
            coeff (argmaxZ coeff (p : ℝ) (Function.update ω x t)) x ^ 2)
      have h := Zdiff_sq_le coeff (p : ℝ) ω x t
      have e : ((-Zproc coeff (p : ℝ) ω) - (-Zproc coeff (p : ℝ) (Function.update ω x t))) ^ 2 =
          (Zproc coeff (p : ℝ) ω - Zproc coeff (p : ℝ) (Function.update ω x t)) ^ 2 := by ring
      rw [e]
      exact h)

end TalagrandCore
end

/-! ## Component: SigmaWeighted -/
section
/-
Weighted first-moment consequence of the self-bounding mgf bound (T1):
for `Y = supProc g` with `0 ≤ g ≤ 1`,

  `Ex[Y·e^{Y/8}] ≤ 24·Ex[Y]·e^{(3/4)·Ex[Y]}`.

The proof splits on `EY := Ex[Y]`:
* `EY = 0`: every weighted term vanishes;
* `0 < EY ≤ 1`: pointwise `Y·e^{Y/8} ≤ e^{1/8}·Y + e^{−s}·e^{(9/8+s)Y}` with
  `s = −log EY`, then T1 at `lam = 9/8 + s` gives
  `Ex[e^{lam·Y}] ≤ exp(e^{9/8} − EY) ≤ exp(e^{9/8}) ≤ 22.5`;
* `EY ≥ 1`: pointwise `Y·e^{Y/8} ≤ 8·e^{Y/4}`, then T1 at `lam = 1/4`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

/-- For `0 ≤ x < 1`, `e^x ≤ 1/(1−x)`. -/
theorem exp_le_one_div_one_sub {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have h3 : 0 < 1 - x := by linarith
  rw [le_div_iff₀ h3]
  calc Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos x).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- Numeric bound `exp(exp(9/8)) ≤ 22.5`. -/
theorem exp_exp_nine_eighths_le : Real.exp (Real.exp (9/8 : ℝ)) ≤ 22.5 := by
  have he1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have he18 : Real.exp (1/8 : ℝ) ≤ 8/7 := by
    calc Real.exp (1/8 : ℝ) ≤ 1 / (1 - 1/8) :=
          exp_le_one_div_one_sub (by norm_num) (by norm_num)
      _ = 8/7 := by norm_num
  have he98 : Real.exp (9/8 : ℝ) ≤ 3.107 := by
    have hsplit : (9/8 : ℝ) = 1 + 1/8 := by norm_num
    rw [hsplit, Real.exp_add]
    calc Real.exp 1 * Real.exp (1/8)
        ≤ 2.7182818286 * (8/7) :=
          mul_le_mul he1 he18 (Real.exp_pos _).le (by norm_num)
      _ ≤ 3.107 := by norm_num
  have h107 : Real.exp (0.107 : ℝ) ≤ 1 / (1 - 0.107) :=
    exp_le_one_div_one_sub (by norm_num) (by norm_num)
  have h3107 : Real.exp (3.107 : ℝ) ≤ 22.5 := by
    have hsplit : (3.107 : ℝ) = 1 + 1 + 1 + 0.107 := by norm_num
    rw [hsplit, Real.exp_add, Real.exp_add, Real.exp_add]
    have e1p : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (0.107 : ℝ)
        ≤ 2.7182818286 * 2.7182818286 * 2.7182818286 * (1 / (1 - 0.107)) := by
          have h11 : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
            mul_le_mul he1 he1 e1p (by norm_num)
          have h111 : Real.exp 1 * Real.exp 1 * Real.exp 1 ≤
              2.7182818286 * 2.7182818286 * 2.7182818286 :=
            mul_le_mul h11 he1 e1p (by norm_num)
          exact mul_le_mul h111 h107 (Real.exp_pos _).le (by norm_num)
      _ ≤ 22.5 := by norm_num
  exact le_trans (Real.exp_le_exp.mpr he98) h3107

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-- **Weighted-moment bound.** For `Y = supProc g` with `0 ≤ g ≤ 1`,
`Ex[Y·e^{Y/8}] ≤ 24·Ex[Y]·e^{(3/4)·Ex[Y]}`. -/
theorem sigma2_weighted_exp (p : NNReal) (hp : p ≤ 1)
    (g : ι → κ → Bool → ℝ) (hg0 : ∀ a x b, 0 ≤ g a x b) (hg1 : ∀ a x b, g a x b ≤ 1) :
    Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8)) ≤
      24 * Ex (p : ℝ) (fun ω => supProc g ω) *
        Real.exp (3 / 4 * Ex (p : ℝ) (fun ω => supProc g ω)) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hY0 : ∀ ω : κ → Bool, 0 ≤ supProc g ω := by
    intro ω
    have a : ι := Classical.arbitrary ι
    exact le_trans (Finset.sum_nonneg fun x _ => hg0 a x (ω x)) (le_supProc g ω a)
  set EY : ℝ := Ex (p : ℝ) (fun ω => supProc g ω) with hEY_def
  have hEY0 : 0 ≤ EY := by rw [hEY_def]; exact Ex_nonneg h0p h1p hY0
  have hexp34 : (1:ℝ) ≤ Real.exp (3 / 4 * EY) := by
    linarith [Real.add_one_le_exp (3 / 4 * EY)]
  rcases eq_or_lt_of_le hEY0 with hEYzero | hEYpos
  · -- Case A : EY = 0.  All the weighted terms vanish.
    have hsum : Ex (p : ℝ) (fun ω => supProc g ω) = 0 := by
      rw [← hEY_def]; exact hEYzero.symm
    have hsum' : ∑ ω : κ → Bool, W (p : ℝ) ω * supProc g ω = 0 := hsum
    have hzero : ∀ ω : κ → Bool, W (p : ℝ) ω * supProc g ω = 0 := fun ω =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun ω _ => mul_nonneg (W_nonneg h0p h1p ω) (hY0 ω))).mp hsum' ω (Finset.mem_univ ω)
    have hLHS : Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8)) = 0 := by
      unfold Ex
      refine Finset.sum_eq_zero fun ω _ => ?_
      calc W (p : ℝ) ω * (supProc g ω * Real.exp (supProc g ω / 8))
          = (W (p : ℝ) ω * supProc g ω) * Real.exp (supProc g ω / 8) := by ring
        _ = 0 := by rw [hzero ω, zero_mul]
    rw [hLHS, ← hEYzero]
    norm_num
  rcases le_total EY 1 with hEY1 | hEY1
  · -- Case B : 0 < EY ≤ 1.
    have hEYne : EY ≠ 0 := ne_of_gt hEYpos
    set s : ℝ := -Real.log EY with hs_def
    have hs0 : 0 ≤ s := by
      rw [hs_def]
      exact neg_nonneg.mpr (Real.log_nonpos hEY0 hEY1)
    have hexp_neg_s : Real.exp (-s) = EY := by
      rw [hs_def, neg_neg, Real.exp_log hEYpos]
    have hexp_s : Real.exp s = EY⁻¹ := by
      rw [hs_def, Real.exp_neg, Real.exp_log hEYpos]
    have hlam0 : (0:ℝ) ≤ 9/8 + s := by linarith
    -- pointwise: `Y·e^{Y/8} ≤ e^{1/8}·Y + e^{−s}·e^{(9/8+s)·Y}`.
    have hpt : ∀ ω : κ → Bool,
        supProc g ω * Real.exp (supProc g ω / 8) ≤
          Real.exp (1/8) * supProc g ω +
            Real.exp (-s) * Real.exp ((9/8 + s) * supProc g ω) := by
      intro ω
      have hy0 := hY0 ω
      rcases le_total (supProc g ω) 1 with hy1 | hy1
      · have h1 : Real.exp (supProc g ω / 8) ≤ Real.exp (1/8) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : supProc g ω * Real.exp (supProc g ω / 8) ≤
            supProc g ω * Real.exp (1/8) := mul_le_mul_of_nonneg_left h1 hy0
        have h3 : 0 ≤ Real.exp (-s) * Real.exp ((9/8 + s) * supProc g ω) := by positivity
        nlinarith
      · have hyexp : supProc g ω ≤ Real.exp (supProc g ω) := by
          linarith [Real.add_one_le_exp (supProc g ω)]
        have h1 : supProc g ω * Real.exp (supProc g ω / 8) ≤
            Real.exp (supProc g ω) * Real.exp (supProc g ω / 8) :=
          mul_le_mul_of_nonneg_right hyexp (Real.exp_pos _).le
        have h2 : Real.exp (supProc g ω) * Real.exp (supProc g ω / 8) =
            Real.exp (9/8 * supProc g ω) := by
          rw [← Real.exp_add]; congr 1; ring
        have h3 : Real.exp (9/8 * supProc g ω) ≤
            Real.exp (-s) * Real.exp ((9/8 + s) * supProc g ω) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hy1)]
        have h4 : 0 ≤ Real.exp (1/8) * supProc g ω :=
          mul_nonneg (Real.exp_pos _).le hy0
        linarith
    -- take expectations
    have hmain : Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8)) ≤
        Real.exp (1/8) * EY +
          Real.exp (-s) * Ex (p : ℝ) (fun ω => Real.exp ((9/8 + s) * supProc g ω)) := by
      calc Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8))
          ≤ Ex (p : ℝ) (fun ω => Real.exp (1/8) * supProc g ω +
              Real.exp (-s) * Real.exp ((9/8 + s) * supProc g ω)) := Ex_mono h0p h1p hpt
        _ = Ex (p : ℝ) (fun ω => Real.exp (1/8) * supProc g ω) +
              Ex (p : ℝ) (fun ω => Real.exp (-s) * Real.exp ((9/8 + s) * supProc g ω)) :=
            Ex_add _ _
        _ = Real.exp (1/8) * EY +
              Real.exp (-s) * Ex (p : ℝ) (fun ω => Real.exp ((9/8 + s) * supProc g ω)) := by
            rw [Ex_smul, Ex_smul, ← hEY_def]
    -- the mgf bound at `lam = 9/8 + s`.
    have hexp_lam_eq : EY * (Real.exp (9/8 + s) - 1) = Real.exp (9/8 : ℝ) - EY := by
      have hring : EY * (Real.exp (9/8 : ℝ) * EY⁻¹ - 1) =
          Real.exp (9/8 : ℝ) * (EY * EY⁻¹) - EY := by ring
      rw [Real.exp_add, hexp_s, hring, mul_inv_cancel₀ hEYne, mul_one]
    have hmgf : Ex (p : ℝ) (fun ω => Real.exp ((9/8 + s) * supProc g ω)) ≤ 22.5 := by
      have h1 := selfbounding_exp_bound p hp g hg0 hg1 (9/8 + s) hlam0
      rw [← hEY_def] at h1
      calc Ex (p : ℝ) (fun ω => Real.exp ((9/8 + s) * supProc g ω))
          ≤ Real.exp (EY * (Real.exp (9/8 + s) - 1)) := h1
        _ ≤ Real.exp (Real.exp (9/8 : ℝ)) := by
            refine Real.exp_le_exp.mpr ?_
            rw [hexp_lam_eq]
            linarith
        _ ≤ 22.5 := exp_exp_nine_eighths_le
    have h18 : Real.exp (1/8 : ℝ) ≤ 8/7 := by
      calc Real.exp (1/8 : ℝ) ≤ 1 / (1 - 1/8) :=
            exp_le_one_div_one_sub (by norm_num) (by norm_num)
        _ = 8/7 := by norm_num
    have hstep : Real.exp (-s) * Ex (p : ℝ) (fun ω => Real.exp ((9/8 + s) * supProc g ω)) ≤
        EY * 22.5 := by
      rw [hexp_neg_s]
      exact mul_le_mul_of_nonneg_left hmgf hEY0
    have hstep2 : Real.exp (1/8) * EY ≤ 8/7 * EY :=
      mul_le_mul_of_nonneg_right h18 hEY0
    have hfinal : Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8)) ≤
        24 * EY := by
      linarith [hmain]
    calc Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8))
        ≤ 24 * EY := hfinal
      _ = 24 * EY * 1 := (mul_one _).symm
      _ ≤ 24 * EY * Real.exp (3 / 4 * EY) :=
          mul_le_mul_of_nonneg_left hexp34 (mul_nonneg (by norm_num) hEY0)
  · -- Case C : 1 ≤ EY.
    have hpt : ∀ ω : κ → Bool,
        supProc g ω * Real.exp (supProc g ω / 8) ≤
          8 * Real.exp (1/4 * supProc g ω) := by
      intro ω
      have hy0 := hY0 ω
      have h1 : supProc g ω / 8 ≤ Real.exp (supProc g ω / 8) := by
        linarith [Real.add_one_le_exp (supProc g ω / 8)]
      have h2 : supProc g ω * Real.exp (supProc g ω / 8) ≤
          8 * Real.exp (supProc g ω / 8) * Real.exp (supProc g ω / 8) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      have h3 : Real.exp (supProc g ω / 8) * Real.exp (supProc g ω / 8) =
          Real.exp (1/4 * supProc g ω) := by
        rw [← Real.exp_add]; congr 1; ring
      calc supProc g ω * Real.exp (supProc g ω / 8)
          ≤ 8 * Real.exp (supProc g ω / 8) * Real.exp (supProc g ω / 8) := h2
        _ = 8 * (Real.exp (supProc g ω / 8) * Real.exp (supProc g ω / 8)) := by ring
        _ = 8 * Real.exp (1/4 * supProc g ω) := by rw [h3]
    have hmgf := selfbounding_exp_bound p hp g hg0 hg1 (1/4) (by norm_num)
    rw [← hEY_def] at hmgf
    have he14 : Real.exp (1/4 : ℝ) ≤ 4/3 := by
      calc Real.exp (1/4 : ℝ) ≤ 1 / (1 - 1/4) :=
            exp_le_one_div_one_sub (by norm_num) (by norm_num)
        _ = 4/3 := by norm_num
    have harg : EY * (Real.exp (1/4 : ℝ) - 1) ≤ 3 / 4 * EY := by
      nlinarith [mul_nonneg hEY0 (sub_nonneg.mpr he14)]
    have hchain : Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8)) ≤
        8 * Real.exp (3 / 4 * EY) := by
      calc Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8))
          ≤ Ex (p : ℝ) (fun ω => 8 * Real.exp (1/4 * supProc g ω)) := Ex_mono h0p h1p hpt
        _ = 8 * Ex (p : ℝ) (fun ω => Real.exp (1/4 * supProc g ω)) := by rw [Ex_smul]
        _ ≤ 8 * Real.exp (EY * (Real.exp (1/4 : ℝ) - 1)) := by linarith [hmgf]
        _ ≤ 8 * Real.exp (3 / 4 * EY) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
    calc Ex (p : ℝ) (fun ω => supProc g ω * Real.exp (supProc g ω / 8))
        ≤ 8 * Real.exp (3 / 4 * EY) := hchain
      _ ≤ 24 * EY * Real.exp (3 / 4 * EY) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end TalagrandCore
end

/-! ## Component: GaussianUpper -/
section
/-
Block T3: the Gaussian–linear Laplace bound for the upper deviation of the
linear supremum `Z` (Ledoux ESAIM'96, (2.14)-(2.16), sign-safe version).

Main results (`v₃ := sigmaSq + Ex[Σ²] + Ex[Z̄]`):

* splitting bound: for `lam ∈ [0,1/8]`,
    `Ex[Σ²·e^{lam Z}] ≤ 30·EΣ²·F + Ex[Z e^{lam Z}] + EZ̄·F`;
* cgf bound: for `lam ∈ [0,1/8]`,
    `log Ex[e^{lam(Z−EZ)}] ≤ 200·lam²·v₃`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-! ### Pointwise facts about `Sigma2`, `Zproc`, `Zbar` -/

/-- `Σ²` is the `supProc` of the squared summands. -/
theorem Sigma2_eq_supProc (coeff : ι → κ → ℝ) (p : ℝ) :
    Sigma2 coeff p =
      supProc (fun a x b => coeff a x ^ 2 * (cond b (1:ℝ) 0 - p) ^ 2) := rfl

theorem sqSummand_nonneg (coeff : ι → κ → ℝ) (p : ℝ) :
    ∀ (a : ι) (x : κ) (b : Bool), 0 ≤ coeff a x ^ 2 * (cond b (1:ℝ) 0 - p) ^ 2 :=
  fun _ _ _ => by positivity

theorem sqSummand_le_one (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    {p : ℝ} (h0p : 0 ≤ p) (h1p : p ≤ 1) :
    ∀ (a : ι) (x : κ) (b : Bool), coeff a x ^ 2 * (cond b (1:ℝ) 0 - p) ^ 2 ≤ 1 := by
  intro a x b
  have hc : coeff a x ^ 2 ≤ 1 := by
    have := hB a x
    nlinarith [abs_nonneg (coeff a x), sq_abs (coeff a x)]
  have hb : (cond b (1:ℝ) 0 - p) ^ 2 ≤ 1 := by
    cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> nlinarith
  nlinarith [sq_nonneg (coeff a x), sq_nonneg (cond b (1:ℝ) 0 - p)]

theorem Sigma2_nonneg (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) :
    0 ≤ Sigma2 coeff p ω := by
  have a : ι := Classical.arbitrary ι
  refine le_trans ?_ (Finset.le_sup'
    (f := fun a : ι => ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - p) ^ 2)
    (Finset.mem_univ a))
  exact Finset.sum_nonneg fun x _ => by positivity

theorem Zbar_nonneg (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) :
    0 ≤ Zbar coeff p ω := by
  have a : ι := Classical.arbitrary ι
  exact le_trans (abs_nonneg _) (Finset.le_sup'
    (f := fun a : ι => |∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x|)
    (Finset.mem_univ a))

theorem Zproc_le_Zbar (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) :
    Zproc coeff p ω ≤ Zbar coeff p ω := by
  unfold Zproc supProc
  apply Finset.sup'_le
  intro a _
  refine le_trans (le_abs_self _) ?_
  exact Finset.le_sup'
    (f := fun a : ι => |∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x|)
    (Finset.mem_univ a)

theorem neg_Zbar_le_Zproc (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) :
    -Zbar coeff p ω ≤ Zproc coeff p ω := by
  have a : ι := Classical.arbitrary ι
  have h1 := le_supProc (linSummand coeff p) ω a
  have h3 : |∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x| ≤ Zbar coeff p ω :=
    Finset.le_sup'
      (f := fun a : ι => |∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x|)
      (Finset.mem_univ a)
  calc -Zbar coeff p ω ≤ -|∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x| := by
        linarith
    _ ≤ ∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x := neg_abs_le _
    _ ≤ Zproc coeff p ω := h1

/-- Sign-safe lower bound: `Z·e^{lam Z} + Z̄ ≥ 0` for `lam ≥ 0`. -/
theorem Z_exp_add_Zbar_nonneg (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool)
    (lam : ℝ) (h0 : 0 ≤ lam) :
    0 ≤ Zproc coeff p ω * Real.exp (lam * Zproc coeff p ω) + Zbar coeff p ω := by
  set Z := Zproc coeff p ω with hZ
  rcases le_or_gt 0 Z with hZ0 | hZ0
  · have hb := Zbar_nonneg coeff p ω
    have hz : 0 ≤ Z * Real.exp (lam * Z) := mul_nonneg hZ0 (Real.exp_pos _).le
    linarith
  · have hexp : Real.exp (lam * Z) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos h0 hZ0.le)
    have h1 : Z ≤ Z * Real.exp (lam * Z) := by
      nlinarith [Real.exp_pos (lam * Z)]
    have h2 := neg_Zbar_le_Zproc coeff p ω
    rw [← hZ] at h2
    linarith

/-! ### Expectation facts: `Ex[Z] ≥ 0`, `F ≥ 1`, `Ex[Z] ≤ Ex[Z̄]` -/

/-- The mean of a single coordinate indicator is `p`. -/
theorem Ex_coord {p : ℝ} (h0p : 0 ≤ p) (h1p : p ≤ 1) (x : κ) :
    Ex p (fun ω : κ → Bool => cond (ω x) (1:ℝ) 0) = p := by
  rw [← Ex_condEx h0p h1p x (fun ω : κ → Bool => cond (ω x) (1:ℝ) 0)]
  have hpt : ∀ ω : κ → Bool,
      condEx p x (fun ω' : κ → Bool => cond (ω' x) (1:ℝ) 0) ω = p := by
    intro ω
    unfold condEx
    simp [Function.update_self, bw]
  rw [Ex_congr hpt, Ex_const h0p h1p]

/-- Each centered linear summand has mean zero. -/
theorem Ex_linSummand_zero {p : ℝ} (h0p : 0 ≤ p) (h1p : p ≤ 1) (x : κ) (c : ℝ) :
    Ex p (fun ω : κ → Bool => (cond (ω x) (1:ℝ) 0 - p) * c) = 0 := by
  have hpt : ∀ ω : κ → Bool,
      (cond (ω x) (1:ℝ) 0 - p) * c =
        c * cond (ω x) (1:ℝ) 0 + (-(p * c)) := fun ω => by ring
  rw [Ex_congr hpt, Ex_add, Ex_smul, Ex_coord h0p h1p x, Ex_const h0p h1p]
  ring

/-- `Ex[Z] ≥ 0` (each linear sum is centered, and `Z` dominates one of them). -/
theorem ExZ_nonneg {p : ℝ} (h0p : 0 ≤ p) (h1p : p ≤ 1) (coeff : ι → κ → ℝ) :
    0 ≤ Ex p (Zproc coeff p) := by
  have a : ι := Classical.arbitrary ι
  have hpt : ∀ ω : κ → Bool,
      ∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x ≤ Zproc coeff p ω :=
    fun ω => le_supProc (linSummand coeff p) ω a
  have hmean : Ex p (fun ω : κ → Bool =>
      ∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x) = 0 := by
    rw [Ex_finsum]
    exact Finset.sum_eq_zero fun x _ => Ex_linSummand_zero h0p h1p x (coeff a x)
  calc (0:ℝ) = Ex p (fun ω : κ → Bool =>
        ∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x) := hmean.symm
    _ ≤ Ex p (Zproc coeff p) := Ex_mono h0p h1p hpt

/-- The mgf of `Z` is at least `1` for `lam ≥ 0`. -/
theorem one_le_F {p : ℝ} (h0p : 0 ≤ p) (h1p : p ≤ 1) (coeff : ι → κ → ℝ)
    (lam : ℝ) (h0 : 0 ≤ lam) :
    1 ≤ Ex p (fun ω => Real.exp (lam * Zproc coeff p ω)) := by
  have hpt : ∀ ω : κ → Bool,
      1 + lam * Zproc coeff p ω ≤ Real.exp (lam * Zproc coeff p ω) := by
    intro ω
    linarith [Real.add_one_le_exp (lam * Zproc coeff p ω)]
  have h1 : Ex p (fun ω : κ → Bool => 1 + lam * Zproc coeff p ω) ≤
      Ex p (fun ω => Real.exp (lam * Zproc coeff p ω)) := Ex_mono h0p h1p hpt
  have h2 : Ex p (fun ω : κ → Bool => 1 + lam * Zproc coeff p ω) =
      1 + lam * Ex p (Zproc coeff p) := by
    have : Ex p (fun ω : κ → Bool => (1:ℝ) + lam * Zproc coeff p ω) =
        Ex p (fun _ : κ → Bool => (1:ℝ)) +
          Ex p (fun ω : κ → Bool => lam * Zproc coeff p ω) := Ex_add _ _
    rw [this, Ex_const h0p h1p, Ex_smul]
  have h3 := ExZ_nonneg h0p h1p coeff
  nlinarith [mul_nonneg h0 h3]

/-- `Ex[Z] ≤ Ex[Z̄]`. -/
theorem ExZ_le_ExZbar {p : ℝ} (h0p : 0 ≤ p) (h1p : p ≤ 1) (coeff : ι → κ → ℝ) :
    Ex p (Zproc coeff p) ≤ Ex p (Zbar coeff p) :=
  Ex_mono h0p h1p fun ω => Zproc_le_Zbar coeff p ω

/-- Pointwise coupling split: on `{Σ² ≤ 6·ES + Z₊}` bound by the linear terms,
off it pay `e^{−(3/4)ES}·Σ²·e^{Σ²/8}` (`lam ∈ [0,1/8]`, `ES ≥ 0`). -/
theorem sigma2_split_pointwise (coeff : ι → κ → ℝ) (p : ℝ)
    (lam ES : ℝ) (h0 : 0 ≤ lam) (h8 : lam ≤ 1/8) (hES : 0 ≤ ES) (ω : κ → Bool) :
    Sigma2 coeff p ω * Real.exp (lam * Zproc coeff p ω) ≤
      6 * ES * Real.exp (lam * Zproc coeff p ω) +
        (Zproc coeff p ω * Real.exp (lam * Zproc coeff p ω) + Zbar coeff p ω) +
        Real.exp (-(3/4) * ES) *
          (Sigma2 coeff p ω * Real.exp (Sigma2 coeff p ω / 8)) := by
  set S := Sigma2 coeff p ω with hSdef
  set Z := Zproc coeff p ω with hZdef
  have hS0 : 0 ≤ S := Sigma2_nonneg coeff p ω
  have hZb0 : 0 ≤ Zbar coeff p ω := Zbar_nonneg coeff p ω
  have hsign : 0 ≤ Z * Real.exp (lam * Z) + Zbar coeff p ω :=
    Z_exp_add_Zbar_nonneg coeff p ω lam h0
  have hexppos : (0:ℝ) < Real.exp (lam * Z) := Real.exp_pos _
  have htail0 : 0 ≤ Real.exp (-(3/4) * ES) * (S * Real.exp (S / 8)) := by positivity
  rcases le_or_gt S (6 * ES + max Z 0) with hcase | hcase
  · -- on-event
    have h1 : S * Real.exp (lam * Z) ≤ (6 * ES + max Z 0) * Real.exp (lam * Z) :=
      mul_le_mul_of_nonneg_right hcase hexppos.le
    have h2 : max Z 0 * Real.exp (lam * Z) ≤
        Z * Real.exp (lam * Z) + Zbar coeff p ω := by
      rcases le_or_gt 0 Z with hZ0 | hZ0
      · rw [max_eq_left hZ0]
        linarith
      · rw [max_eq_right hZ0.le, zero_mul]
        exact hsign
    nlinarith [h1, h2]
  · -- off-event: `lam·Z ≤ (S − 6·ES)/8`.
    have hZp0 : 0 ≤ max Z 0 := le_max_right Z 0
    have hlZ : lam * Z ≤ (S - 6 * ES) / 8 := by
      have e1 : lam * Z ≤ lam * max Z 0 :=
        mul_le_mul_of_nonneg_left (le_max_left Z 0) h0
      have e2 : lam * max Z 0 ≤ (1/8) * max Z 0 :=
        mul_le_mul_of_nonneg_right h8 hZp0
      have e3 : max Z 0 ≤ S - 6 * ES := by linarith
      nlinarith [e2, e3]
    have hsplit : Real.exp ((S - 6 * ES) / 8) =
        Real.exp (-(3/4) * ES) * Real.exp (S / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h1 : S * Real.exp (lam * Z) ≤ S * Real.exp ((S - 6 * ES) / 8) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlZ) hS0
    have h2 : S * Real.exp ((S - 6 * ES) / 8) =
        Real.exp (-(3/4) * ES) * (S * Real.exp (S / 8)) := by
      rw [hsplit]; ring
    have h3 : 0 ≤ 6 * ES * Real.exp (lam * Z) := by positivity
    linarith [h1, h2 ▸ h1]

/-- Splitting bound (Ledoux p.79, fixed-exponent version):
`Ex[Σ²·e^{lam Z}] ≤ 30·EΣ²·F + Ex[Z e^{lam Z}] + EZ̄·F` on `[0,1/8]`. -/
theorem sigma2_coupling_split (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (lam : ℝ) (h0 : 0 ≤ lam) (h8 : lam ≤ 1/8) :
    Ex (p : ℝ) (fun ω => Sigma2 coeff (p : ℝ) ω *
        Real.exp (lam * Zproc coeff (p : ℝ) ω)) ≤
      30 * Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) *
          Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω)) +
        Ex (p : ℝ) (fun ω => Zproc coeff (p : ℝ) ω *
          Real.exp (lam * Zproc coeff (p : ℝ) ω)) +
        Ex (p : ℝ) (Zbar coeff (p : ℝ)) *
          Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω)) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set ES : ℝ := Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) with hES_def
  set F : ℝ := Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω)) with hF_def
  set Gd : ℝ := Ex (p : ℝ) (fun ω => Zproc coeff (p : ℝ) ω *
    Real.exp (lam * Zproc coeff (p : ℝ) ω)) with hGd_def
  set EZb : ℝ := Ex (p : ℝ) (Zbar coeff (p : ℝ)) with hEZb_def
  have hES0 : 0 ≤ ES := Ex_nonneg h0p h1p (Sigma2_nonneg coeff (p : ℝ))
  have hEZb0 : 0 ≤ EZb := Ex_nonneg h0p h1p (Zbar_nonneg coeff (p : ℝ))
  have hF1 : 1 ≤ F := one_le_F h0p h1p coeff lam h0
  -- expectation of the pointwise split
  have hmono : Ex (p : ℝ) (fun ω => Sigma2 coeff (p : ℝ) ω *
        Real.exp (lam * Zproc coeff (p : ℝ) ω)) ≤
      Ex (p : ℝ) (fun ω =>
        6 * ES * Real.exp (lam * Zproc coeff (p : ℝ) ω) +
          (Zproc coeff (p : ℝ) ω * Real.exp (lam * Zproc coeff (p : ℝ) ω) +
            Zbar coeff (p : ℝ) ω) +
          Real.exp (-(3/4) * ES) *
            (Sigma2 coeff (p : ℝ) ω * Real.exp (Sigma2 coeff (p : ℝ) ω / 8))) :=
    Ex_mono h0p h1p (fun ω => sigma2_split_pointwise coeff (p : ℝ) lam ES h0 h8 hES0 ω)
  -- split the expectation
  have e1 : Ex (p : ℝ) (fun ω =>
        6 * ES * Real.exp (lam * Zproc coeff (p : ℝ) ω) +
          (Zproc coeff (p : ℝ) ω * Real.exp (lam * Zproc coeff (p : ℝ) ω) +
            Zbar coeff (p : ℝ) ω) +
          Real.exp (-(3/4) * ES) *
            (Sigma2 coeff (p : ℝ) ω * Real.exp (Sigma2 coeff (p : ℝ) ω / 8))) =
      6 * ES * F + (Gd + EZb) +
        Real.exp (-(3/4) * ES) * Ex (p : ℝ) (fun ω =>
          Sigma2 coeff (p : ℝ) ω * Real.exp (Sigma2 coeff (p : ℝ) ω / 8)) := by
    rw [Ex_add, Ex_add, Ex_smul, Ex_smul, Ex_add]
  -- the weighted-moment bound (T1 consequence)
  have hW : Ex (p : ℝ) (fun ω =>
        Sigma2 coeff (p : ℝ) ω * Real.exp (Sigma2 coeff (p : ℝ) ω / 8)) ≤
      24 * ES * Real.exp (3 / 4 * ES) :=
    sigma2_weighted_exp p hp
      (fun a x b => coeff a x ^ 2 * (cond b (1:ℝ) 0 - (p : ℝ)) ^ 2)
      (sqSummand_nonneg coeff (p : ℝ)) (sqSummand_le_one coeff hB h0p h1p)
  have hC : Real.exp (-(3/4) * ES) * Ex (p : ℝ) (fun ω =>
        Sigma2 coeff (p : ℝ) ω * Real.exp (Sigma2 coeff (p : ℝ) ω / 8)) ≤ 24 * ES := by
    have h1 := mul_le_mul_of_nonneg_left hW (Real.exp_pos (-(3/4) * ES)).le
    have h2 : Real.exp (-(3/4) * ES) * (24 * ES * Real.exp (3 / 4 * ES)) = 24 * ES := by
      have hee : Real.exp (-(3/4) * ES) * Real.exp (3 / 4 * ES) = 1 := by
        rw [← Real.exp_add]
        norm_num
      calc Real.exp (-(3/4) * ES) * (24 * ES * Real.exp (3 / 4 * ES))
          = 24 * ES * (Real.exp (-(3/4) * ES) * Real.exp (3 / 4 * ES)) := by ring
        _ = 24 * ES := by rw [hee]; ring
    linarith
  -- combine, absorbing `24·ES` and `EZ̄` with `F ≥ 1`
  have hcomb : Ex (p : ℝ) (fun ω => Sigma2 coeff (p : ℝ) ω *
      Real.exp (lam * Zproc coeff (p : ℝ) ω)) ≤ 6 * ES * F + Gd + EZb + 24 * ES := by
    rw [e1] at hmono
    linarith
  have habs1 : 24 * ES ≤ 24 * ES * F := by nlinarith
  have habs2 : EZb ≤ EZb * F := by nlinarith
  linarith

/-- The Gaussian differential inequality on `[0,1/8]`, obtained from the
two-copy entropy bound (T2) and the splitting bound:
`l·Gd(l) − F(l)·log F(l) ≤ (4/3)·l²·(A·F(l) + Gd(l))` with
`A = sigmaSq + 30·EΣ² + EZ̄`. -/
theorem gaussian_DI (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (sigmaSq : ℝ) (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    (l : ℝ) (h0l : 0 ≤ l) (h8l : l ≤ 1/8) :
    l * Ex (p : ℝ) (fun ω => Zproc coeff (p : ℝ) ω *
        Real.exp (l * Zproc coeff (p : ℝ) ω)) -
      Ex (p : ℝ) (fun ω => Real.exp (l * Zproc coeff (p : ℝ) ω)) *
        Real.log (Ex (p : ℝ) (fun ω => Real.exp (l * Zproc coeff (p : ℝ) ω))) ≤
      4/3 * l ^ 2 *
        ((sigmaSq + 30 * Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
            Ex (p : ℝ) (Zbar coeff (p : ℝ))) *
            Ex (p : ℝ) (fun ω => Real.exp (l * Zproc coeff (p : ℝ) ω)) +
          Ex (p : ℝ) (fun ω => Zproc coeff (p : ℝ) ω *
            Real.exp (l * Zproc coeff (p : ℝ) ω))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set F : ℝ := Ex (p : ℝ) (fun ω => Real.exp (l * Zproc coeff (p : ℝ) ω)) with hF_def
  set Gd : ℝ := Ex (p : ℝ) (fun ω => Zproc coeff (p : ℝ) ω *
    Real.exp (l * Zproc coeff (p : ℝ) ω)) with hGd_def
  set X : ℝ := Ex (p : ℝ) (fun ω => Real.exp (l * Zproc coeff (p : ℝ) ω) *
    (Sigma2 coeff (p : ℝ) ω + sigmaSq)) with hX_def
  have hT2 := two_copy_entropy_Z p hp coeff hB sigmaSq hVar l h0l
  have hX0 : 0 ≤ X := Ex_nonneg h0p h1p fun ω =>
    mul_nonneg (Real.exp_pos _).le (by linarith [Sigma2_nonneg coeff (p : ℝ) ω])
  have hXsplit : X = Ex (p : ℝ) (fun ω => Sigma2 coeff (p : ℝ) ω *
      Real.exp (l * Zproc coeff (p : ℝ) ω)) + sigmaSq * F := by
    rw [hX_def]
    have hpt : ∀ ω : κ → Bool,
        Real.exp (l * Zproc coeff (p : ℝ) ω) * (Sigma2 coeff (p : ℝ) ω + sigmaSq) =
          Sigma2 coeff (p : ℝ) ω * Real.exp (l * Zproc coeff (p : ℝ) ω) +
            sigmaSq * Real.exp (l * Zproc coeff (p : ℝ) ω) := fun ω => by ring
    rw [Ex_congr hpt, Ex_add, Ex_smul]
  have hexp2l : Real.exp (2 * l) ≤ 4/3 := by
    calc Real.exp (2 * l) ≤ Real.exp (1/4 : ℝ) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / (1 - 1/4) := exp_le_one_div_one_sub (by norm_num) (by norm_num)
      _ = 4/3 := by norm_num
  have hsc := sigma2_coupling_split p hp coeff hB l h0l h8l
  have hXle : X ≤ (sigmaSq + 30 * Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
      Ex (p : ℝ) (Zbar coeff (p : ℝ))) * F + Gd := by
    rw [hXsplit]
    nlinarith [hsc]
  have step1 : l ^ 2 * Real.exp (2 * l) * X ≤ 4/3 * l ^ 2 * X := by
    have h1 : 0 ≤ 4/3 - Real.exp (2 * l) := by linarith
    have h2 : 0 ≤ l ^ 2 * X := mul_nonneg (sq_nonneg l) hX0
    nlinarith [mul_nonneg h1 h2]
  have step2 : 4/3 * l ^ 2 * X ≤ 4/3 * l ^ 2 *
      ((sigmaSq + 30 * Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
        Ex (p : ℝ) (Zbar coeff (p : ℝ))) * F + Gd) :=
    mul_le_mul_of_nonneg_left hXle (by positivity)
  calc l * Gd - F * Real.log F ≤ l ^ 2 * Real.exp (2 * l) * X := hT2
    _ ≤ 4/3 * l ^ 2 * X := step1
    _ ≤ _ := step2

/-- ODE comparison for `u = log F`: for `lam ∈ (0,1/8]`,
`u(lam) ≤ lam·EZ + (4/3)·A·lam² + (4/3)·lam·u(lam)` with
`A = sigmaSq + 30·EΣ² + EZ̄`. -/
theorem gaussian_log_mgf_ineq (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (sigmaSq : ℝ) (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    (lam : ℝ) (hpos : 0 < lam) (h8 : lam ≤ 1/8) :
    Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω))) ≤
      lam * Ex (p : ℝ) (Zproc coeff (p : ℝ)) +
        4/3 * (sigmaSq + 30 * Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
          Ex (p : ℝ) (Zbar coeff (p : ℝ))) * lam ^ 2 +
        4/3 * lam * Real.log (Ex (p : ℝ)
          (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set Y : (κ → Bool) → ℝ := Zproc coeff (p : ℝ) with hY_def
  set A : ℝ := sigmaSq + 30 * Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
    Ex (p : ℝ) (Zbar coeff (p : ℝ)) with hA_def
  set EZ : ℝ := Ex (p : ℝ) Y with hEZ_def
  set F : ℝ → ℝ := fun l => Ex (p : ℝ) (fun ω => Real.exp (l * Y ω)) with hF_def
  set Gd : ℝ → ℝ := fun l => Ex (p : ℝ) (fun ω => Y ω * Real.exp (l * Y ω)) with hGd_def
  have hFpos : ∀ l, 0 < F l := fun l => Ex_pos h0p h1p (fun ω => Real.exp_pos _)
  have hFderiv : ∀ l, HasDerivAt F (Gd l) l := fun l => hasDerivAt_ExExp (p : ℝ) Y l
  have hF0 : F 0 = 1 := by
    show Ex (p : ℝ) (fun ω => Real.exp ((0:ℝ) * Y ω)) = 1
    have h1 : (fun ω : κ → Bool => Real.exp ((0:ℝ) * Y ω)) = fun _ => (1:ℝ) := by
      funext ω; simp
    rw [h1, Ex_const h0p h1p]
  set u : ℝ → ℝ := fun l => Real.log (F l) with hu_def
  have hu0 : u 0 = 0 := by rw [hu_def]; simp [hF0]
  have huderiv : ∀ l, HasDerivAt u (Gd l / F l) l := fun l =>
    (hFderiv l).log (ne_of_gt (hFpos l))
  -- the comparison function `M`
  set M : ℝ → ℝ := fun l => 4/3 * A * l + 4/3 * u l - u l / l with hM_def
  have hMderiv : ∀ l : ℝ, 0 < l → HasDerivAt M
      (4/3 * A * 1 + 4/3 * (Gd l / F l) -
        (Gd l / F l * l - u l * 1) / l ^ 2) l := by
    intro l hl
    have h1 : HasDerivAt (fun x : ℝ => 4/3 * A * x) (4/3 * A * 1) l :=
      (hasDerivAt_id l).const_mul (4/3 * A)
    have h2 : HasDerivAt (fun x : ℝ => 4/3 * u x) (4/3 * (Gd l / F l)) l :=
      (huderiv l).const_mul (4/3)
    have h3 : HasDerivAt (fun x : ℝ => u x / x)
        ((Gd l / F l * l - u l * 1) / l ^ 2) l :=
      (huderiv l).div (hasDerivAt_id l) (ne_of_gt hl)
    exact (h1.add h2).sub h3
  -- `M' ≥ 0` on the interior, from the differential inequality
  have hMmono : MonotoneOn M (Set.Ioc 0 lam) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 lam)
    · intro l hl
      exact (hMderiv l hl.1).continuousAt.continuousWithinAt
    · intro l hl
      rw [interior_Ioc] at hl
      exact (hMderiv l hl.1).differentiableAt.differentiableWithinAt
    · intro l hl
      rw [interior_Ioc] at hl
      rw [(hMderiv l hl.1).deriv]
      have hl0 : 0 < l := hl.1
      have hl2 : (0:ℝ) < l ^ 2 := by positivity
      have hFl := hFpos l
      have hDIl : l * Gd l - F l * Real.log (F l) ≤ 4/3 * l ^ 2 * (A * F l + Gd l) :=
        gaussian_DI p hp coeff hB sigmaSq hs hVar l hl0.le (le_trans hl.2.le h8)
      have hGdF : Gd l / F l * F l = Gd l := div_mul_cancel₀ _ (ne_of_gt hFl)
      have hu_eq : u l = Real.log (F l) := rfl
      have hdiv : l * (Gd l / F l) - Real.log (F l) ≤
          4/3 * l ^ 2 * (A + Gd l / F l) := by
        have h' : (l * (Gd l / F l) - Real.log (F l)) * F l ≤
            (4/3 * l ^ 2 * (A + Gd l / F l)) * F l := by
          calc (l * (Gd l / F l) - Real.log (F l)) * F l
              = l * (Gd l / F l * F l) - F l * Real.log (F l) := by ring
            _ = l * Gd l - F l * Real.log (F l) := by rw [hGdF]
            _ ≤ 4/3 * l ^ 2 * (A * F l + Gd l) := hDIl
            _ = 4/3 * l ^ 2 * (A * F l + Gd l / F l * F l) := by rw [hGdF]
            _ = (4/3 * l ^ 2 * (A + Gd l / F l)) * F l := by ring
        exact le_of_mul_le_mul_right h' hFl
      have hfin : (Gd l / F l * l - u l * 1) / l ^ 2 ≤
          4/3 * A + 4/3 * (Gd l / F l) := by
        rw [div_le_iff₀ hl2, hu_eq]
        nlinarith [hdiv]
      linarith [hfin]
  -- endpoint limit: `M a → −EZ` as `a → 0⁺`
  have hslope : Filter.Tendsto (fun a => u a / a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds EZ) := by
    have h1 := (huderiv 0).tendsto_slope
    have hval : Gd 0 / F 0 = EZ := by
      rw [hF0, div_one, hGd_def, hEZ_def]
      exact Ex_congr fun ω => by simp
    rw [hval] at h1
    have heq : (fun a => u a / a) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] slope u 0 := by
      refine Filter.eventually_of_mem self_mem_nhdsWithin fun a ha => ?_
      rw [slope_def_field, hu0, sub_zero, sub_zero]
    exact Filter.Tendsto.congr' heq.symm
      (h1.mono_left (nhdsWithin_mono 0 fun a ha => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt ha))
  have hucont : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 := (huderiv 0).continuousAt.tendsto
    rw [hu0] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hMtend : Filter.Tendsto M (nhdsWithin 0 (Set.Ioi 0)) (nhds (-EZ)) := by
    have hlin : Filter.Tendsto (fun a : ℝ => 4/3 * A * a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : Filter.Tendsto (fun a : ℝ => 4/3 * A * a)
          (nhds 0) (nhds (4/3 * A * 0)) := (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have hcomb := (hlin.add (hucont.const_mul (4/3 : ℝ))).sub hslope
    have hz : (0:ℝ) + 4/3 * 0 - EZ = -EZ := by ring
    rw [hz] at hcomb
    exact hcomb
  have hev : ∀ᶠ a in nhdsWithin 0 (Set.Ioi 0), M a ≤ M lam := by
    have hmem : Set.Ioo (0:ℝ) lam ∈ nhdsWithin 0 (Set.Ioi 0) := by
      apply mem_nhdsWithin.mpr
      exact ⟨Set.Iio lam, isOpen_Iio, hpos, fun a ⟨ha1, ha2⟩ => ⟨ha2, ha1⟩⟩
    filter_upwards [hmem] with a ha
    exact hMmono (Set.mem_Ioc.mpr ⟨ha.1, ha.2.le⟩)
      (Set.mem_Ioc.mpr ⟨hpos, le_refl lam⟩) ha.2.le
  have hkey : -EZ ≤ M lam := le_of_tendsto hMtend hev
  -- unfold and rearrange
  have hMlam : M lam = 4/3 * A * lam + 4/3 * u lam - u lam / lam := rfl
  rw [hMlam] at hkey
  have h1 : u lam / lam ≤ EZ + 4/3 * A * lam + 4/3 * u lam := by linarith
  have h2 : u lam ≤ (EZ + 4/3 * A * lam + 4/3 * u lam) * lam :=
    (div_le_iff₀ hpos).mp h1
  show u lam ≤ lam * EZ + 4/3 * A * lam ^ 2 + 4/3 * lam * u lam
  calc u lam ≤ (EZ + 4/3 * A * lam + 4/3 * u lam) * lam := h2
    _ = lam * EZ + 4/3 * A * lam ^ 2 + 4/3 * lam * u lam := by ring

/-- **T3 (Gaussian-linear cgf bound for the upper tail).** -/
theorem gaussian_upper_cgf (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (sigmaSq : ℝ) (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    (lam : ℝ) (h0 : 0 ≤ lam) (h8 : lam ≤ 1/8) :
    Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam *
        (Zproc coeff (p : ℝ) ω - Ex (p : ℝ) (Zproc coeff (p : ℝ)))))) ≤
      200 * lam ^ 2 *
        (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
          Ex (p : ℝ) (Zbar coeff (p : ℝ))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  rcases eq_or_lt_of_le h0 with heq | hpos
  · -- `lam = 0`: both sides vanish.
    rw [← heq]
    have h1 : (fun ω : κ → Bool => Real.exp ((0:ℝ) *
        (Zproc coeff (p : ℝ) ω - Ex (p : ℝ) (Zproc coeff (p : ℝ))))) =
        fun _ => (1:ℝ) := by
      funext ω; simp
    rw [h1, Ex_const h0p h1p, Real.log_one]
    norm_num
  · -- main case `lam > 0`
    set EZ : ℝ := Ex (p : ℝ) (Zproc coeff (p : ℝ)) with hEZ_def
    set ES2 : ℝ := Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) with hES2_def
    set EZb : ℝ := Ex (p : ℝ) (Zbar coeff (p : ℝ)) with hEZb_def
    set u : ℝ := Real.log (Ex (p : ℝ)
      (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω))) with hu_def
    have hES20 : 0 ≤ ES2 := Ex_nonneg h0p h1p (Sigma2_nonneg coeff (p : ℝ))
    have hEZb0 : 0 ≤ EZb := Ex_nonneg h0p h1p (Zbar_nonneg coeff (p : ℝ))
    have hEZ0 : 0 ≤ EZ := ExZ_nonneg h0p h1p coeff
    have hEZle : EZ ≤ EZb := ExZ_le_ExZbar h0p h1p coeff
    have hu0 : 0 ≤ u := Real.log_nonneg (one_le_F h0p h1p coeff lam h0)
    have hFpos : 0 < Ex (p : ℝ)
        (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω)) :=
      Ex_pos h0p h1p fun ω => Real.exp_pos _
    have hkey : u ≤ lam * EZ + 4/3 * (sigmaSq + 30 * ES2 + EZb) * lam ^ 2 +
        4/3 * lam * u :=
      gaussian_log_mgf_ineq p hp coeff hB sigmaSq hs hVar lam hpos h8
    -- bootstrap: absorb `(4/3)·lam·u ≤ (1/6)·u`
    have h43 : 4/3 * lam * u ≤ 1/6 * u := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ 1/6 - 4/3 * lam by linarith) hu0]
    have pass1 : u ≤ 6/5 * (lam * EZ) +
        8/5 * (sigmaSq + 30 * ES2 + EZb) * lam ^ 2 := by
      linarith
    have h2 : 4/3 * lam * u ≤ 4/3 * lam * (6/5 * (lam * EZ) +
        8/5 * (sigmaSq + 30 * ES2 + EZb) * lam ^ 2) :=
      mul_le_mul_of_nonneg_left pass1 (by linarith)
    have pass2 : u - lam * EZ ≤ 4/3 * (sigmaSq + 30 * ES2 + EZb) * lam ^ 2 +
        4/3 * lam * (6/5 * (lam * EZ) +
          8/5 * (sigmaSq + 30 * ES2 + EZb) * lam ^ 2) := by
      linarith
    -- identify the left-hand side
    have hLHS : Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam *
        (Zproc coeff (p : ℝ) ω - EZ)))) = u - lam * EZ := by
      have hpt : ∀ ω : κ → Bool,
          Real.exp (lam * (Zproc coeff (p : ℝ) ω - EZ)) =
            Real.exp (-(lam * EZ)) * Real.exp (lam * Zproc coeff (p : ℝ) ω) := by
        intro ω
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Ex_congr hpt, Ex_smul,
        Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hFpos), Real.log_exp, ← hu_def]
      ring
    rw [hLHS]
    -- final arithmetic: `lam³ ≤ lam²/8`, `EZ ≤ EZ̄`, nonnegativity
    have hl3 : lam ^ 3 ≤ 1/8 * lam ^ 2 := by
      have h := mul_le_mul_of_nonneg_right h8 (sq_nonneg lam)
      calc lam ^ 3 = lam * lam ^ 2 := by ring
        _ ≤ 1/8 * lam ^ 2 := h
    nlinarith [pass2, hl3, sq_nonneg lam,
      mul_nonneg (sq_nonneg lam) hs, mul_nonneg (sq_nonneg lam) hES20,
      mul_nonneg (sq_nonneg lam) hEZb0,
      mul_le_mul_of_nonneg_left hEZle (sq_nonneg lam),
      mul_le_mul_of_nonneg_left hl3 (show (0:ℝ) ≤ sigmaSq + 30 * ES2 + EZb by linarith)]

end TalagrandCore
end

/-! ## Component: PoissonTail -/
section
/-
T1a: the Poissonian upper tail for nonnegative self-bounding sup-processes,
from `selfbounding_exp_bound` by Chernoff at `lam = log (s/m)`:

  P(Y ≥ s) ≤ exp(−(s·log(s/m) − s + m))   for  EY ≤ m,  0 < m ≤ s.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-- Chernoff upper-tail transfer for an arbitrary function. -/
theorem chernoff_upper {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (Y : (κ → Bool) → ℝ) {lam s : ℝ} (hlam : 0 ≤ lam) :
    Ex p (fun ω => if s ≤ Y ω then (1:ℝ) else 0) ≤
      Real.exp (-(lam * s)) * Ex p (fun ω => Real.exp (lam * Y ω)) := by
  have hpt : ∀ ω, (if s ≤ Y ω then (1:ℝ) else 0) ≤
      Real.exp (-(lam * s)) * Real.exp (lam * Y ω) := by
    intro ω
    rw [← Real.exp_add]
    split
    · rename_i h
      rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left h hlam
      nlinarith
    · exact (Real.exp_pos _).le
  calc Ex p (fun ω => if s ≤ Y ω then (1:ℝ) else 0) ≤
      Ex p (fun ω => Real.exp (-(lam * s)) * Real.exp (lam * Y ω)) :=
        Ex_mono h0 h1 hpt
    _ = Real.exp (-(lam * s)) * Ex p (fun ω => Real.exp (lam * Y ω)) :=
        Ex_smul _ _

/-- **T1a (Poisson tail).** For a nonnegative `[0,1]`-summand sup-process
with mean at most `m`, `P(Y ≥ s) ≤ exp(−(s·log(s/m) − s + m))` for `0 < m ≤ s`. -/
theorem poisson_tail (p : NNReal) (hp : p ≤ 1)
    (g : ι → κ → Bool → ℝ) (hg0 : ∀ a x b, 0 ≤ g a x b)
    (hg1 : ∀ a x b, g a x b ≤ 1) {m s : ℝ}
    (hm : Ex (p : ℝ) (fun ω => supProc g ω) ≤ m) (hm0 : 0 < m) (hms : m ≤ s) :
    Ex (p : ℝ) (fun ω => if s ≤ supProc g ω then (1:ℝ) else 0) ≤
      Real.exp (-(s * Real.log (s / m) - s + m)) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set lam := Real.log (s / m) with hlam
  have hspos : 0 < s := lt_of_lt_of_le hm0 hms
  have hlam0 : 0 ≤ lam := Real.log_nonneg ((one_le_div hm0).mpr hms)
  have hexplam : Real.exp lam = s / m := Real.exp_log (div_pos hspos hm0)
  have hmgf := selfbounding_exp_bound p hp g hg0 hg1 lam hlam0
  have hEY0 : 0 ≤ Ex (p : ℝ) (fun ω => supProc g ω) := by
    apply Ex_nonneg h0p h1p
    intro ω
    obtain ⟨a⟩ := (inferInstance : Nonempty ι)
    refine le_trans ?_ (le_supProc g ω a)
    exact Finset.sum_nonneg fun x _ => hg0 a x (ω x)
  have hmono : Ex (p : ℝ) (fun ω => supProc g ω) * (Real.exp lam - 1) ≤
      m * (Real.exp lam - 1) := by
    apply mul_le_mul_of_nonneg_right hm
    rw [hexplam]
    have : (1:ℝ) ≤ s / m := (one_le_div hm0).mpr hms
    linarith
  calc Ex (p : ℝ) (fun ω => if s ≤ supProc g ω then (1:ℝ) else 0) ≤
      Real.exp (-(lam * s)) *
        Ex (p : ℝ) (fun ω => Real.exp (lam * supProc g ω)) :=
        chernoff_upper h0p h1p (supProc g) hlam0
    _ ≤ Real.exp (-(lam * s)) *
        Real.exp (Ex (p : ℝ) (fun ω => supProc g ω) * (Real.exp lam - 1)) := by
        apply mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ ≤ Real.exp (-(lam * s)) * Real.exp (m * (Real.exp lam - 1)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmono)
          (Real.exp_pos _).le
    _ = Real.exp (-(s * Real.log (s / m) - s + m)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hexplam]
        field_simp
        ring

end TalagrandCore
end

/-! ## Component: Symmetrization -/
section
/-
Block T6: the symmetrization/contraction bound

  `Ex[Σ²] ≤ sigmaSq + 8·Ex[Z̄]`     (B = 1)

(Ledoux–Talagrand Lemmas 6.3 & 6.6 chain: center the squares, symmetrize with
an independent copy and Rademacher signs, apply the `u ↦ u²` contraction on
`[−1,1]`, then desymmetrize back to `2·E Z̄`.)

All expectations are finite sums, and the symmetrization copies live on the
doubled cube `(κ → Bool) × (κ → Bool)` with an auxiliary Rademacher factor
`κ → Bool` — still finite, so everything stays in sum-land.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-! ### Rademacher signs and the masked pair swap -/

/-- Real-valued Rademacher sign of a Boolean. -/
def sg (b : Bool) : ℝ := cond b (-1) 1

theorem sg_not (b : Bool) : sg (!b) = - sg b := by cases b <;> simp [sg]

theorem sg_true : sg true = -1 := rfl
theorem sg_false : sg false = 1 := rfl

/-- Swap the two copies at exactly the coordinates where `s` is true. -/
def mix (s ω ω' : κ → Bool) : κ → Bool := fun x => cond (s x) (ω' x) (ω x)

theorem mix_mix (s ω ω' : κ → Bool) : mix s (mix s ω ω') (mix s ω' ω) = ω := by
  funext x; cases hs : s x <;> simp [mix, hs]

theorem W_mix_mul (p : ℝ) (s ω ω' : κ → Bool) :
    W p (mix s ω ω') * W p (mix s ω' ω) = W p ω * W p ω' := by
  unfold W
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  cases hs : s x <;> simp [mix, hs, mul_comm]

theorem bw_half_true : bw (1/2 : ℝ) true = 1/2 := rfl

theorem bw_half_false : bw (1/2 : ℝ) false = 1/2 := by norm_num [bw]

/-! ### Double expectations: product form, masked-swap invariance, Fubini -/

theorem ExEx_eq_sum_prod (p : ℝ) (H : (κ → Bool) → (κ → Bool) → ℝ) :
    Ex p (fun ω => Ex p (fun ω' => H ω ω')) =
      ∑ z : (κ → Bool) × (κ → Bool), W p z.1 * W p z.2 * H z.1 z.2 := by
  unfold Ex
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω' _ => by ring

/-- Masked pair-swap invariance of the doubled expectation. -/
theorem ExEx_mix (p : ℝ) (s : κ → Bool) (H : (κ → Bool) → (κ → Bool) → ℝ) :
    Ex p (fun ω => Ex p (fun ω' => H ω ω')) =
      Ex p (fun ω => Ex p (fun ω' => H (mix s ω ω') (mix s ω' ω))) := by
  rw [ExEx_eq_sum_prod, ExEx_eq_sum_prod]
  refine Finset.sum_nbij' (i := fun z => (mix s z.1 z.2, mix s z.2 z.1))
    (j := fun z => (mix s z.1 z.2, mix s z.2 z.1)) ?_ ?_ ?_ ?_ ?_
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact Prod.ext (mix_mix s z.1 z.2) (mix_mix s z.2 z.1)
  · intro z _; exact Prod.ext (mix_mix s z.1 z.2) (mix_mix s z.2 z.1)
  · intro z _
    show W p z.1 * W p z.2 * H z.1 z.2 =
      W p (mix s z.1 z.2) * W p (mix s z.2 z.1) *
        H (mix s (mix s z.1 z.2) (mix s z.2 z.1)) (mix s (mix s z.2 z.1) (mix s z.1 z.2))
    rw [mix_mix s z.1 z.2, mix_mix s z.2 z.1, W_mix_mul]

/-- Fubini for the nested finite expectations. -/
theorem ExEx_swap (p q : ℝ) (F : (κ → Bool) → (κ → Bool) → ℝ) :
    Ex p (fun s => Ex q (fun ω => F s ω)) = Ex q (fun ω => Ex p (fun s => F s ω)) := by
  unfold Ex
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun s _ => by ring

/-- At `p = 1/2`, flipping all sign bits is expectation-preserving. -/
theorem Ex_half_not (F : (κ → Bool) → ℝ) :
    Ex (1/2 : ℝ) (fun s => F (fun x => !(s x))) = Ex (1/2 : ℝ) F := by
  unfold Ex
  refine Finset.sum_nbij' (i := fun s x => !(s x)) (j := fun s x => !(s x)) ?_ ?_ ?_ ?_ ?_
  · intro s _; exact Finset.mem_univ _
  · intro s _; exact Finset.mem_univ _
  · intro s _; funext x; simp
  · intro s _; funext x; simp
  · intro s _
    show W (1/2 : ℝ) s * F (fun x => !(s x)) =
      W (1/2 : ℝ) (fun x => !(s x)) * F (fun x => !(s x))
    have hbw : ∀ b, bw (1/2 : ℝ) b = 1/2 := by
      intro b; cases b
      · exact bw_half_false
      · exact bw_half_true
    have hW : W (1/2 : ℝ) (fun x => !(s x)) = W (1/2 : ℝ) s := by
      unfold W
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [hbw, hbw]
    rw [hW]

/-! ### Coordinate expectations and `sup'` helpers -/

/-- Expectation of a function of a single coordinate. -/
theorem Ex_coordFn {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : κ) (g : Bool → ℝ) :
    Ex p (fun ω => g (ω x)) = p * g true + (1 - p) * g false := by
  rw [← Ex_condEx h0 h1 x (fun ω => g (ω x))]
  have hc : ∀ ω : κ → Bool,
      condEx p x (fun ω' => g (ω' x)) ω = p * g true + (1 - p) * g false := by
    intro ω; unfold condEx
    simp [Function.update_self, bw]
  rw [Ex_congr hc, Ex_const h0 h1]

/-- Jensen for the finite supremum: `max_a E[g_a] ≤ E[max_a g_a]`. -/
theorem sup'_Ex_le_Ex_sup' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (g : ι → (κ → Bool) → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun a : ι => Ex p (g a)) ≤
      Ex p (fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => g a ω)) := by
  apply Finset.sup'_le
  intro a _
  exact Ex_mono h0 h1 fun ω =>
    Finset.le_sup' (f := fun a : ι => g a ω) (Finset.mem_univ a)

theorem sup'_const_mul (c : ℝ) (hc : 0 ≤ c) (f : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun a : ι => c * f a) =
      c * Finset.univ.sup' Finset.univ_nonempty f := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (f := f) (Finset.mem_univ a)) hc
  · obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) f
    rw [ha]
    exact Finset.le_sup' (f := fun a : ι => c * f a) (Finset.mem_univ a)

/-! ### The two-point contraction step -/

/-- Two-point core of the `v ↦ v²` contraction principle on `[-1,1]`. -/
theorem contraction_step (t v : ι → ℝ) (hv : ∀ a, |v a| ≤ 1) :
    Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg true * v c ^ 2) +
      Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg false * v c ^ 2) ≤
    Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg true * (2 * v c)) +
      Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg false * (2 * v c)) := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι))
    (fun c : ι => t c + sg true * v c ^ 2)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι))
    (fun c : ι => t c + sg false * v c ^ 2)
  rw [ha, hb]
  have hva := abs_le.mp (hv a)
  have hvb := abs_le.mp (hv b)
  have hsgt : sg true = -1 := rfl
  have hsgf : sg false = 1 := rfl
  rcases le_total (v b) (v a) with hle | hle
  · have h1 : t a + sg false * (2 * v a) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg false * (2 * v c)) :=
      Finset.le_sup' (f := fun c : ι => t c + sg false * (2 * v c)) (Finset.mem_univ a)
    have h2 : t b + sg true * (2 * v b) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg true * (2 * v c)) :=
      Finset.le_sup' (f := fun c : ι => t c + sg true * (2 * v c)) (Finset.mem_univ b)
    rw [hsgf] at h1
    rw [hsgt] at h2
    rw [hsgt, hsgf]
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (by linarith : (0:ℝ) ≤ v a + v b + 2)]
  · have h1 : t a + sg true * (2 * v a) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg true * (2 * v c)) :=
      Finset.le_sup' (f := fun c : ι => t c + sg true * (2 * v c)) (Finset.mem_univ a)
    have h2 : t b + sg false * (2 * v b) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg false * (2 * v c)) :=
      Finset.le_sup' (f := fun c : ι => t c + sg false * (2 * v c)) (Finset.mem_univ b)
    rw [hsgt] at h1
    rw [hsgf] at h2
    rw [hsgt, hsgf]
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (by linarith : (0:ℝ) ≤ 2 - (v a + v b))]

/-- Averaged (Bernoulli-1/2) form of the two-point contraction step. -/
theorem contraction_half (t v : ι → ℝ) (hv : ∀ a, |v a| ≤ 1) :
    bw (1/2 : ℝ) true *
        Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg true * v c ^ 2) +
      bw (1/2 : ℝ) false *
        Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg false * v c ^ 2) ≤
    bw (1/2 : ℝ) true *
        Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg true * (2 * v c)) +
      bw (1/2 : ℝ) false *
        Finset.univ.sup' Finset.univ_nonempty (fun c : ι => t c + sg false * (2 * v c)) := by
  rw [bw_half_true, bw_half_false]
  have h := contraction_step t v hv
  linarith

/-! ### Splitting signed sums at an updated coordinate -/

theorem sum_sg_update_of_notmem {S : Finset κ} {x₀ : κ} (hx₀ : x₀ ∉ S)
    (s : κ → Bool) (tv : Bool) (f : κ → ℝ) :
    ∑ x ∈ S, sg (Function.update s x₀ tv x) * f x = ∑ x ∈ S, sg (s x) * f x :=
  Finset.sum_congr rfl fun x hx => by
    rw [Function.update_apply, if_neg (by rintro rfl; exact hx₀ hx)]

theorem sum_sg_update_insert {S : Finset κ} {x₀ : κ} (hx₀ : x₀ ∉ S)
    (s : κ → Bool) (tv : Bool) (f : κ → ℝ) :
    ∑ x ∈ insert x₀ S, sg (Function.update s x₀ tv x) * f x =
      sg tv * f x₀ + ∑ x ∈ S, sg (s x) * f x := by
  rw [Finset.sum_insert hx₀, Function.update_self, sum_sg_update_of_notmem hx₀]

theorem sum_sg_update_compl {S : Finset κ} {x₀ : κ} (hx₀ : x₀ ∉ S)
    (s : κ → Bool) (tv : Bool) (f : κ → ℝ) :
    ∑ x ∈ Sᶜ, sg (Function.update s x₀ tv x) * f x =
      sg tv * f x₀ + ∑ x ∈ (insert x₀ S)ᶜ, sg (s x) * f x := by
  have hmem : x₀ ∈ Sᶜ := Finset.mem_compl.mpr hx₀
  rw [← Finset.add_sum_erase _ _ hmem, Function.update_self]
  congr 1
  rw [Finset.compl_insert]
  exact Finset.sum_congr rfl fun x hx => by
    rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hx)]

theorem sup'_ins_update (u : ι → κ → ℝ) (S' : Finset κ) (x₀ : κ) (hx₀ : x₀ ∉ S')
    (s : κ → Bool) (tv : Bool) :
    Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
        (∑ x ∈ insert x₀ S', sg (Function.update s x₀ tv x) * u a x ^ 2) +
          ∑ x ∈ (insert x₀ S')ᶜ, sg (Function.update s x₀ tv x) * (2 * u a x)) =
      Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
        ((∑ x ∈ S', sg (s x) * u a x ^ 2) +
            ∑ x ∈ (insert x₀ S')ᶜ, sg (s x) * (2 * u a x)) + sg tv * u a x₀ ^ 2) := by
  refine Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => ?_
  rw [sum_sg_update_insert hx₀,
    sum_sg_update_of_notmem
      (fun h => (Finset.mem_compl.mp h) (Finset.mem_insert_self x₀ S')) s tv]
  ring

theorem sup'_lin_update (u : ι → κ → ℝ) (S' : Finset κ) (x₀ : κ) (hx₀ : x₀ ∉ S')
    (s : κ → Bool) (tv : Bool) :
    Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
        (∑ x ∈ S', sg (Function.update s x₀ tv x) * u a x ^ 2) +
          ∑ x ∈ S'ᶜ, sg (Function.update s x₀ tv x) * (2 * u a x)) =
      Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
        ((∑ x ∈ S', sg (s x) * u a x ^ 2) +
            ∑ x ∈ (insert x₀ S')ᶜ, sg (s x) * (2 * u a x)) + sg tv * (2 * u a x₀)) := by
  refine Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => ?_
  rw [sum_sg_update_of_notmem hx₀, sum_sg_update_compl hx₀]
  ring

/-- **Contraction main induction**: replacing signed squares by signed doubled
linear terms, one coordinate at a time, only increases the Rademacher average. -/
theorem contraction_main (u : ι → κ → ℝ) (hu : ∀ a x, |u a x| ≤ 1) (S : Finset κ) :
    Ex (1/2 : ℝ) (fun s : κ → Bool =>
        Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
          (∑ x ∈ S, sg (s x) * u a x ^ 2) + ∑ x ∈ Sᶜ, sg (s x) * (2 * u a x))) ≤
      Ex (1/2 : ℝ) (fun s : κ → Bool =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun a : ι => ∑ x : κ, sg (s x) * (2 * u a x))) := by
  have h0 : (0:ℝ) ≤ 1/2 := by norm_num
  have h1 : (1/2:ℝ) ≤ 1 := by norm_num
  induction S using Finset.induction_on with
  | empty =>
    refine le_of_eq (Ex_congr fun s => ?_)
    simp only [Finset.sum_empty, Finset.compl_empty, zero_add]
  | @insert x₀ S' hx₀ ih =>
    refine le_trans ?_ ih
    rw [← Ex_condEx h0 h1 x₀ (fun s : κ → Bool =>
        Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
          (∑ x ∈ insert x₀ S', sg (s x) * u a x ^ 2) +
            ∑ x ∈ (insert x₀ S')ᶜ, sg (s x) * (2 * u a x))),
      ← Ex_condEx h0 h1 x₀ (fun s : κ → Bool =>
        Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
          (∑ x ∈ S', sg (s x) * u a x ^ 2) + ∑ x ∈ S'ᶜ, sg (s x) * (2 * u a x)))]
    refine Ex_mono h0 h1 fun s => ?_
    simp only [condEx]
    rw [sup'_ins_update u S' x₀ hx₀ s true, sup'_ins_update u S' x₀ hx₀ s false,
      sup'_lin_update u S' x₀ hx₀ s true, sup'_lin_update u S' x₀ hx₀ s false]
    exact contraction_half
      (fun a : ι => (∑ x ∈ S', sg (s x) * u a x ^ 2) +
        ∑ x ∈ (insert x₀ S')ᶜ, sg (s x) * (2 * u a x))
      (fun a : ι => u a x₀) (fun a => hu a x₀)

/-! ### Symmetrization processes -/

/-- Generic sign-introduction on the doubled cube: for coordinate summands,
the masked swap turns the plain difference process into the signed one. -/
theorem ExEx_mix_sign (P : ℝ) (s : κ → Bool) (g : ι → κ → Bool → ℝ) :
    Ex P (fun ω => Ex P (fun ω' =>
      Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
        ∑ x : κ, (g a x (ω x) - g a x (ω' x))))) =
    Ex P (fun ω => Ex P (fun ω' =>
      Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
        ∑ x : κ, sg (s x) * (g a x (ω x) - g a x (ω' x))))) := by
  rw [ExEx_mix P s (fun ω ω' =>
    Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
      ∑ x : κ, (g a x (ω x) - g a x (ω' x))))]
  refine Ex_congr fun ω => Ex_congr fun ω' => ?_
  refine Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  show g a x (mix s ω ω' x) - g a x (mix s ω' ω x) =
    sg (s x) * (g a x (ω x) - g a x (ω' x))
  cases hs : s x <;> simp [mix, hs, sg]

/-- Centered squares process. -/
noncomputable def Vsup (coeff : ι → κ → ℝ) (P : ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
      P * (1 - P) * coeff a x ^ 2))

/-- Doubled (two-copy) squares-difference process. -/
noncomputable def Dsq (coeff : ι → κ → ℝ) (P : ℝ) (ω ω' : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
      ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2))

/-- Signed doubled squares-difference process. -/
noncomputable def Hsq (coeff : ι → κ → ℝ) (P : ℝ) (s ω ω' : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, sg (s x) * (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
      ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2))

/-- Rademacher squares process. -/
noncomputable def Asq (coeff : ι → κ → ℝ) (P : ℝ) (s ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2)

/-- Rademacher linear process. -/
noncomputable def Alin (coeff : ι → κ → ℝ) (P : ℝ) (s ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x))

theorem abs_linterm_le {P : ℝ} (h0 : 0 ≤ P) (h1 : P ≤ 1) {c : ℝ} (hc : |c| ≤ 1)
    (b : Bool) : |(cond b (1:ℝ) 0 - P) * c| ≤ 1 := by
  have h : |cond b (1:ℝ) 0 - P| ≤ 1 := by
    cases b
    · show |(0:ℝ) - P| ≤ 1
      rw [zero_sub, abs_neg, abs_of_nonneg h0]; exact h1
    · show |(1:ℝ) - P| ≤ 1
      rw [abs_of_nonneg (by linarith)]; linarith
  calc |(cond b (1:ℝ) 0 - P) * c| = |cond b (1:ℝ) 0 - P| * |c| := abs_mul _ _
    _ ≤ 1 * 1 := mul_le_mul h hc (abs_nonneg c) (by norm_num)
    _ = 1 := mul_one 1

/-- Triangle inequality into `Zbar` for the plain doubled linear process. -/
theorem sup'_pairdiff_le_Zbar (coeff : ι → κ → ℝ) (P : ℝ) (ω ω' : κ → Bool) :
    Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
        ∑ x : κ, ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
          (cond (ω' x) (1:ℝ) 0 - P) * coeff a x)) ≤
      Zbar coeff P ω + Zbar coeff P ω' := by
  apply Finset.sup'_le
  intro a _
  rw [Finset.sum_sub_distrib]
  have h1 : |∑ x : κ, (cond (ω x) (1:ℝ) 0 - P) * coeff a x| ≤ Zbar coeff P ω :=
    Finset.le_sup'
      (f := fun a : ι => |∑ x : κ, (cond (ω x) (1:ℝ) 0 - P) * coeff a x|)
      (Finset.mem_univ a)
  have h2 : |∑ x : κ, (cond (ω' x) (1:ℝ) 0 - P) * coeff a x| ≤ Zbar coeff P ω' :=
    Finset.le_sup'
      (f := fun a : ι => |∑ x : κ, (cond (ω' x) (1:ℝ) 0 - P) * coeff a x|)
      (Finset.mem_univ a)
  have h3 := le_abs_self (∑ x : κ, (cond (ω x) (1:ℝ) 0 - P) * coeff a x)
  have h4 := neg_abs_le (∑ x : κ, (cond (ω' x) (1:ℝ) 0 - P) * coeff a x)
  linarith

/-- Pointwise: `Σ² ≤ sigmaSq + Vsup`. -/
theorem Sigma2_le_pointwise {P : ℝ} (coeff : ι → κ → ℝ) (sigmaSq : ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, P * (1 - P) * coeff a x ^ 2 ≤ sigmaSq)
    (ω : κ → Bool) :
    Sigma2 coeff P ω ≤ sigmaSq + Vsup coeff P ω := by
  unfold Sigma2
  apply Finset.sup'_le
  intro a _
  have hsplit : ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - P) ^ 2 =
      (∑ x : κ, P * (1 - P) * coeff a x ^ 2) +
        ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
          P * (1 - P) * coeff a x ^ 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsplit]
  have h2 : ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
      P * (1 - P) * coeff a x ^ 2) ≤ Vsup coeff P ω :=
    Finset.le_sup'
      (f := fun a : ι => ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
        P * (1 - P) * coeff a x ^ 2))
      (Finset.mem_univ a)
  have h3 := hVar a
  linarith

/-- Centering plus Jensen: `E[Vsup] ≤ E E[Dsq]`. -/
theorem Ex_Vsup_le_ExEx_Dsq {P : ℝ} (h0 : 0 ≤ P) (h1 : P ≤ 1)
    (coeff : ι → κ → ℝ) :
    Ex P (Vsup coeff P) ≤
      Ex P (fun ω => Ex P (fun ω' => Dsq coeff P ω ω')) := by
  refine Ex_mono h0 h1 fun ω => ?_
  have hcen : ∀ a : ι,
      (∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
        P * (1 - P) * coeff a x ^ 2)) =
      Ex P (fun ω' => ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
        ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2)) := by
    intro a
    rw [Ex_finsum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h := Ex_coordFn h0 h1 x (fun b =>
      ((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
        ((cond b (1:ℝ) 0 - P) * coeff a x) ^ 2)
    refine Eq.symm (h.trans ?_)
    show P * (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
        ((1 - P) * coeff a x) ^ 2) +
      (1 - P) * (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
        ((0 - P) * coeff a x) ^ 2) =
      ((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 - P * (1 - P) * coeff a x ^ 2
    ring
  unfold Vsup
  calc Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
        ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
          P * (1 - P) * coeff a x ^ 2))
      = Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
          Ex P (fun ω' => ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
            ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2))) :=
        Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => hcen a
    _ ≤ Ex P (fun ω' => Dsq coeff P ω ω') :=
        sup'_Ex_le_Ex_sup' h0 h1 (fun a ω' =>
          ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
            ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2))

/-- Sign introduction for the doubled squares process. -/
theorem ExEx_Dsq_eq_Hsq {P : ℝ} (coeff : ι → κ → ℝ) (s : κ → Bool) :
    Ex P (fun ω => Ex P (fun ω' => Dsq coeff P ω ω')) =
      Ex P (fun ω => Ex P (fun ω' => Hsq coeff P s ω ω')) :=
  ExEx_mix_sign P s (fun a x b => ((cond b (1:ℝ) 0 - P) * coeff a x) ^ 2)

/-- Triangle for the signed squares process. -/
theorem Hsq_le_Asq_add (coeff : ι → κ → ℝ) (P : ℝ) (s ω ω' : κ → Bool) :
    Hsq coeff P s ω ω' ≤
      Asq coeff P s ω + Asq coeff P (fun x => !(s x)) ω' := by
  unfold Hsq Asq
  apply Finset.sup'_le
  intro a _
  have hsp : ∑ x : κ, sg (s x) * (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
        ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2) =
      (∑ x : κ, sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2) +
        ∑ x : κ, sg (!(s x)) * ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [sg_not]
    ring
  rw [hsp]
  exact add_le_add
    (Finset.le_sup'
      (f := fun a : ι => ∑ x : κ,
        sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2)
      (Finset.mem_univ a))
    (Finset.le_sup'
      (f := fun a : ι => ∑ x : κ,
        sg (!(s x)) * ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2)
      (Finset.mem_univ a))

/-- Per fixed sign pattern: split the doubled signed squares expectation. -/
theorem ExEx_Hsq_le {P : ℝ} (h0 : 0 ≤ P) (h1 : P ≤ 1)
    (coeff : ι → κ → ℝ) (s : κ → Bool) :
    Ex P (fun ω => Ex P (fun ω' => Hsq coeff P s ω ω')) ≤
      Ex P (Asq coeff P s) + Ex P (Asq coeff P (fun x => !(s x))) := by
  calc Ex P (fun ω => Ex P (fun ω' => Hsq coeff P s ω ω'))
      ≤ Ex P (fun ω => Ex P (fun ω' =>
          Asq coeff P s ω + Asq coeff P (fun x => !(s x)) ω')) :=
        Ex_mono h0 h1 fun ω => Ex_mono h0 h1 fun ω' =>
          Hsq_le_Asq_add coeff P s ω ω'
    _ = Ex P (fun ω => Asq coeff P s ω +
          Ex P (Asq coeff P (fun x => !(s x)))) := by
        refine Ex_congr fun ω => ?_
        rw [Ex_add]
        rw [Ex_const h0 h1]
    _ = Ex P (Asq coeff P s) + Ex P (Asq coeff P (fun x => !(s x))) := by
        rw [Ex_add]
        rw [Ex_const h0 h1]

/-- Per fixed configuration: contraction from signed squares to signed
doubled linear terms. -/
theorem Ex_Asq_le_two_Alin {P : ℝ} (h0 : 0 ≤ P) (h1 : P ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1) (ω : κ → Bool) :
    Ex (1/2 : ℝ) (fun s => Asq coeff P s ω) ≤
      2 * Ex (1/2 : ℝ) (fun s => Alin coeff P s ω) := by
  have hu : ∀ (a : ι) (x : κ), |(cond (ω x) (1:ℝ) 0 - P) * coeff a x| ≤ 1 :=
    fun a x => abs_linterm_le h0 h1 (hB a x) (ω x)
  have hmain := contraction_main
    (fun a x => (cond (ω x) (1:ℝ) 0 - P) * coeff a x) hu Finset.univ
  calc Ex (1/2 : ℝ) (fun s => Asq coeff P s ω)
      = Ex (1/2 : ℝ) (fun s : κ → Bool =>
          Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
            (∑ x ∈ Finset.univ, sg (s x) *
              ((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2) +
            ∑ x ∈ (Finset.univ : Finset κ)ᶜ, sg (s x) *
              (2 * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x)))) := by
        refine Ex_congr fun s => ?_
        unfold Asq
        refine Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => ?_
        rw [Finset.compl_univ, Finset.sum_empty, add_zero]
    _ ≤ Ex (1/2 : ℝ) (fun s : κ → Bool =>
          Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
            ∑ x : κ, sg (s x) *
              (2 * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x)))) := hmain
    _ = Ex (1/2 : ℝ) (fun s => 2 * Alin coeff P s ω) := by
        refine Ex_congr fun s => ?_
        unfold Alin
        rw [← sup'_const_mul 2 (by norm_num)]
        refine Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = 2 * Ex (1/2 : ℝ) (fun s => Alin coeff P s ω) :=
        Ex_smul 2 (fun s => Alin coeff P s ω)

/-- Desymmetrization: for every fixed sign pattern, the expected signed
linear supremum is at most `2·E[Z̄]`. -/
theorem Ex_Alin_le_two_Zbar {P : ℝ} (h0 : 0 ≤ P) (h1 : P ≤ 1)
    (coeff : ι → κ → ℝ) (s : κ → Bool) :
    Ex P (fun ω => Alin coeff P s ω) ≤ 2 * Ex P (Zbar coeff P) := by
  calc Ex P (fun ω => Alin coeff P s ω)
      ≤ Ex P (fun ω => Ex P (fun ω' =>
          Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
            ∑ x : κ, sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
              (cond (ω' x) (1:ℝ) 0 - P) * coeff a x)))) := by
        refine Ex_mono h0 h1 fun ω => ?_
        have hcen : ∀ a : ι,
            (∑ x : κ, sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x)) =
            Ex P (fun ω' => ∑ x : κ, sg (s x) *
              ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
                (cond (ω' x) (1:ℝ) 0 - P) * coeff a x)) := by
          intro a
          rw [Ex_finsum]
          refine Finset.sum_congr rfl fun x _ => ?_
          have h := Ex_coordFn h0 h1 x (fun b =>
            sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
              (cond b (1:ℝ) 0 - P) * coeff a x))
          refine Eq.symm (h.trans ?_)
          show P * (sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
              (1 - P) * coeff a x)) +
            (1 - P) * (sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
              (0 - P) * coeff a x)) =
            sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x)
          ring
        unfold Alin
        calc Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
              ∑ x : κ, sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x))
            = Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
                Ex P (fun ω' => ∑ x : κ, sg (s x) *
                  ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
                    (cond (ω' x) (1:ℝ) 0 - P) * coeff a x))) :=
              Finset.sup'_congr Finset.univ_nonempty rfl fun a _ => hcen a
          _ ≤ Ex P (fun ω' =>
                Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
                  ∑ x : κ, sg (s x) *
                    ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
                      (cond (ω' x) (1:ℝ) 0 - P) * coeff a x))) :=
              sup'_Ex_le_Ex_sup' h0 h1 (fun a ω' =>
                ∑ x : κ, sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
                  (cond (ω' x) (1:ℝ) 0 - P) * coeff a x))
    _ = Ex P (fun ω => Ex P (fun ω' =>
          Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
            ∑ x : κ, ((cond (ω x) (1:ℝ) 0 - P) * coeff a x -
              (cond (ω' x) (1:ℝ) 0 - P) * coeff a x)))) :=
        (ExEx_mix_sign P s (fun a x b => (cond b (1:ℝ) 0 - P) * coeff a x)).symm
    _ ≤ Ex P (fun ω => Ex P (fun ω' => Zbar coeff P ω + Zbar coeff P ω')) :=
        Ex_mono h0 h1 fun ω => Ex_mono h0 h1 fun ω' =>
          sup'_pairdiff_le_Zbar coeff P ω ω'
    _ = 2 * Ex P (Zbar coeff P) := by
        have hin : ∀ ω : κ → Bool,
            Ex P (fun ω' => Zbar coeff P ω + Zbar coeff P ω') =
              Zbar coeff P ω + Ex P (Zbar coeff P) := by
          intro ω
          rw [Ex_add]
          rw [Ex_const h0 h1]
        rw [Ex_congr hin, Ex_add, Ex_const h0 h1]
        ring

/-- The full symmetrization/contraction/desymmetrization chain:
`E[Vsup] ≤ 2·2·2·E[Z̄]`. -/
theorem Ex_Vsup_le_eight_Zbar {P : ℝ} (h0 : 0 ≤ P) (h1 : P ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1) :
    Ex P (Vsup coeff P) ≤ 8 * Ex P (Zbar coeff P) := by
  have h0h : (0:ℝ) ≤ 1/2 := by norm_num
  have h1h : (1/2:ℝ) ≤ 1 := by norm_num
  calc Ex P (Vsup coeff P)
      ≤ Ex P (fun ω => Ex P (fun ω' => Dsq coeff P ω ω')) :=
        Ex_Vsup_le_ExEx_Dsq h0 h1 coeff
    _ = Ex (1/2 : ℝ) (fun _ : κ → Bool =>
          Ex P (fun ω => Ex P (fun ω' => Dsq coeff P ω ω'))) :=
        (Ex_const h0h h1h _).symm
    _ = Ex (1/2 : ℝ) (fun s : κ → Bool =>
          Ex P (fun ω => Ex P (fun ω' => Hsq coeff P s ω ω'))) :=
        Ex_congr fun s => ExEx_Dsq_eq_Hsq coeff s
    _ ≤ Ex (1/2 : ℝ) (fun s : κ → Bool =>
          Ex P (Asq coeff P s) + Ex P (Asq coeff P (fun x => !(s x)))) :=
        Ex_mono h0h h1h fun s => ExEx_Hsq_le h0 h1 coeff s
    _ = Ex (1/2 : ℝ) (fun s => Ex P (Asq coeff P s)) +
          Ex (1/2 : ℝ) (fun s => Ex P (Asq coeff P (fun x => !(s x)))) :=
        Ex_add _ _
    _ = Ex (1/2 : ℝ) (fun s => Ex P (Asq coeff P s)) +
          Ex (1/2 : ℝ) (fun s => Ex P (Asq coeff P s)) :=
        congrArg₂ (· + ·) rfl (Ex_half_not (fun s => Ex P (Asq coeff P s)))
    _ = 2 * Ex (1/2 : ℝ) (fun s => Ex P (Asq coeff P s)) := by ring
    _ = 2 * Ex P (fun ω => Ex (1/2 : ℝ) (fun s => Asq coeff P s ω)) :=
        congrArg (fun r => 2 * r)
          (ExEx_swap (1/2 : ℝ) P (fun s ω => Asq coeff P s ω))
    _ ≤ 2 * Ex P (fun ω => 2 * Ex (1/2 : ℝ) (fun s => Alin coeff P s ω)) := by
        have h := Ex_mono h0 h1 fun ω => Ex_Asq_le_two_Alin h0 h1 coeff hB ω
        linarith
    _ = 2 * (2 * Ex P (fun ω => Ex (1/2 : ℝ) (fun s => Alin coeff P s ω))) :=
        congrArg (fun r => 2 * r)
          (Ex_smul 2 (fun ω => Ex (1/2 : ℝ) (fun s => Alin coeff P s ω)))
    _ = 2 * (2 * Ex (1/2 : ℝ) (fun s => Ex P (fun ω => Alin coeff P s ω))) :=
        congrArg (fun r => 2 * (2 * r))
          (ExEx_swap (1/2 : ℝ) P (fun s ω => Alin coeff P s ω)).symm
    _ ≤ 2 * (2 * Ex (1/2 : ℝ) (fun _ : κ → Bool => 2 * Ex P (Zbar coeff P))) := by
        have h := Ex_mono h0h h1h fun s => Ex_Alin_le_two_Zbar h0 h1 coeff s
        linarith
    _ = 8 * Ex P (Zbar coeff P) := by
        rw [Ex_const h0h h1h]
        ring

/-- **T6 (variance-process expectation bound).** -/
theorem sigma2_expectation_bound (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (sigmaSq : ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq) :
    Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) ≤
      sigmaSq + 8 * Ex (p : ℝ) (Zbar coeff (p : ℝ)) := by
  have h0 : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1 : ((p : ℝ)) ≤ 1 := by exact_mod_cast hp
  calc Ex (p : ℝ) (Sigma2 coeff (p : ℝ))
      ≤ Ex (p : ℝ) (fun ω => sigmaSq + Vsup coeff (p : ℝ) ω) :=
        Ex_mono h0 h1 fun ω => Sigma2_le_pointwise coeff sigmaSq hVar ω
    _ = sigmaSq + Ex (p : ℝ) (Vsup coeff (p : ℝ)) := by
        rw [Ex_add]
        rw [Ex_const h0 h1]
    _ ≤ sigmaSq + 8 * Ex (p : ℝ) (Zbar coeff (p : ℝ)) := by
        have h := Ex_Vsup_le_eight_Zbar h0 h1 coeff hB
        linarith

end TalagrandCore
end

/-! ## Component: KRFunctions -/
section
/-
Single-variable calculus lemmas from T. Klein and E. Rio, "Concentration
around the mean for maxima of empirical processes", Ann. Probab. 33 (2005),
Sections 4.2 and 5.

Contents (pure real analysis, no probability, no integrals):
* `psiKR t = (e^{2t} + 1)/2` and `phiKR t = psiKR t * log (psiKR t)`, with
  basic facts (`psiKR_ge_one`, `phiKR_zero`, `phiKR_nonneg`, `phiKR_mono`,
  `cosh_le_psiKR`).
* The monotone-ratio fact behind Lemma 4.4: `x ↦ x⁻²(1 + (x−1)eˣ)` (extended
  by continuity with value `1/2` at `0`) is nondecreasing on the real line
  (`lemma44_g_mono`), and its pointwise consequence `lemma44_consequence`.
* Lemma 4.5: `t ≤ phiKR t` for all `t ≥ 0` (`lemma45_lower`) and
  `phiKR t ≤ t·e^{2t} − t²/2` for `t ∈ [0, 1/2]` (`lemma45_upper`); the paper
  states the upper bound on `[0, t₀]` with `t₀ < 1/2` and its §5 proof works
  on all of `[0, 1/2]`.

The integral-based Lemma 4.6 (functions `I`, `J`) is intentionally omitted.
-/

namespace TalagrandCore

open Real

/-! ### Generic derivative-sign helpers (mirrors of `nonneg_of_deriv_nonneg_Ici`) -/

/-- A function vanishing at `0` with nonnegative derivative on `(−∞,0)` is
nonpositive on `(−∞,0]`. -/
theorem nonpos_of_deriv_nonneg_Iic {f f' : ℝ → ℝ}
    (hf : ∀ x, x ≤ 0 → HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hd : ∀ x, x < 0 → 0 ≤ f' x) :
    ∀ u, u ≤ 0 → f u ≤ 0 := by
  have hmono : MonotoneOn f (Set.Iic (0:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
    · intro x hx
      exact (hf x (Set.mem_Iic.mp hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Iic] at hx
      exact ((hf x (Set.mem_Iio.mp hx).le).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Iic] at hx
      rw [(hf x (Set.mem_Iio.mp hx).le).deriv]
      exact hd x (Set.mem_Iio.mp hx)
  intro u hu
  have := hmono (Set.mem_Iic.mpr hu) Set.self_mem_Iic hu
  linarith [h0 ▸ this]

/-- A function vanishing at the left endpoint of `[a,b]`, with nonnegative
derivative on `(a,b)`, is nonnegative on `[a,b]`. -/
theorem nonneg_of_deriv_nonneg_Icc {a b : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ x, x ∈ Set.Icc a b → HasDerivAt f (f' x) x)
    (h0 : f a = 0) (hd : ∀ x, x ∈ Set.Ioo a b → 0 ≤ f' x) :
    ∀ u, u ∈ Set.Icc a b → 0 ≤ f u := by
  have hmono : MonotoneOn f (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hf x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hf x (Set.Ioo_subset_Icc_self hx)).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hf x (Set.Ioo_subset_Icc_self hx)).deriv]
      exact hd x hx
  intro u hu
  have hab : a ≤ b := le_trans hu.1 hu.2
  have := hmono (Set.left_mem_Icc.mpr hab) hu hu.1
  linarith [h0 ▸ this]

/-- Version-robust monotonicity of `log` on positives. -/
private theorem log_le_log' {x y : ℝ} (hx : 0 < x) (h : x ≤ y) :
    Real.log x ≤ Real.log y := by
  rw [← Real.exp_le_exp, Real.exp_log hx, Real.exp_log (lt_of_lt_of_le hx h)]
  exact h

/-! ### The Klein–Rio functions `ψ` and `φ` -/

/-- Klein–Rio §4.2: `ψ(t) = (e^{2t} + 1)/2`. -/
noncomputable def psiKR (t : ℝ) : ℝ := (Real.exp (2*t) + 1) / 2

/-- Klein–Rio §4.2: `φ(t) = ψ(t)·log ψ(t)`. -/
noncomputable def phiKR (t : ℝ) : ℝ := psiKR t * Real.log (psiKR t)

theorem psiKR_pos (t : ℝ) : 0 < psiKR t := by
  unfold psiKR; positivity

theorem psiKR_ge_one (t : ℝ) (ht : 0 ≤ t) : 1 ≤ psiKR t := by
  unfold psiKR
  have := Real.one_le_exp (by linarith : (0:ℝ) ≤ 2*t)
  linarith

theorem phiKR_zero : phiKR 0 = 0 := by
  unfold phiKR psiKR
  norm_num

theorem phiKR_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ phiKR t := by
  have h1 := psiKR_ge_one t ht
  have h2 := Real.log_nonneg h1
  exact mul_nonneg (by linarith) h2

/-- `φ` is nondecreasing on `[0,∞)`: both factors `ψ` and `log ψ` are
nonnegative and nondecreasing there. -/
theorem phiKR_mono : MonotoneOn phiKR (Set.Ici (0:ℝ)) := by
  intro s hs t ht hst
  have hs0 : (0:ℝ) ≤ s := Set.mem_Ici.mp hs
  have hψs : 1 ≤ psiKR s := psiKR_ge_one s hs0
  have hψst : psiKR s ≤ psiKR t := by
    unfold psiKR
    have : Real.exp (2*s) ≤ Real.exp (2*t) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hlog : Real.log (psiKR s) ≤ Real.log (psiKR t) :=
    log_le_log' (psiKR_pos s) hψst
  have hlog0 : 0 ≤ Real.log (psiKR s) := Real.log_nonneg hψs
  exact mul_le_mul hψst hlog hlog0 (by linarith)

/-- Klein–Rio (proof of Lemma 4.2): `cosh t ≤ ψ(t) = (e^{2t}+1)/2` for `t ≥ 0`. -/
theorem cosh_le_psiKR (t : ℝ) (ht : 0 ≤ t) :
    Real.cosh t ≤ (Real.exp (2*t) + 1) / 2 := by
  rw [Real.cosh_eq]
  have ha : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hapos : 0 < Real.exp t := Real.exp_pos t
  have hbpos : 0 < Real.exp (-t) := Real.exp_pos _
  have h2 : Real.exp (2*t) = Real.exp t * Real.exp t := by
    rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; simp
  rw [h2]
  have key : Real.exp t + Real.exp (-t) ≤ Real.exp t * Real.exp t + 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_self_nonneg (Real.exp t)),
      hinv, hapos, hbpos, ha]
  linarith

/-! ### Auxiliary hyperbolic estimates for Lemma 4.5 -/

/-- `ψ(t) = eᵗ · cosh t`. -/
private theorem psiKR_eq_exp_mul_cosh (t : ℝ) :
    psiKR t = Real.exp t * Real.cosh t := by
  rw [Real.cosh_eq]
  unfold psiKR
  have h2 : Real.exp (2*t) = Real.exp t * Real.exp t := by
    rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; simp
  rw [h2]
  linear_combination (-1/2 : ℝ) * hinv

/-- `log ψ(t) = t + log cosh t`. -/
private theorem log_psiKR (t : ℝ) :
    Real.log (psiKR t) = t + Real.log (Real.cosh t) := by
  rw [psiKR_eq_exp_mul_cosh, Real.log_mul (Real.exp_ne_zero t) (Real.cosh_pos t).ne',
    Real.log_exp]

/-- `sinh x ≤ x·cosh x` for `x ≥ 0`. -/
private theorem sinh_le_mul_cosh (x : ℝ) (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun y => y * Real.cosh y - Real.sinh y)
    (f' := fun y => y * Real.sinh y)
    (fun y _ => by
      have h1 : HasDerivAt (fun z : ℝ => z * Real.cosh z)
          (1 * Real.cosh y + y * Real.sinh y) y :=
        (hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)
      have := h1.sub (Real.hasDerivAt_sinh y)
      exact this.congr_deriv (by ring))
    (by simp)
    (fun y hy => mul_nonneg hy.le (Real.sinh_nonneg_iff.mpr hy.le))
    x hx
  linarith

/-- `log cosh x ≤ x²/2` for `x ≥ 0`. -/
private theorem log_cosh_le (x : ℝ) (hx : 0 ≤ x) :
    Real.log (Real.cosh x) ≤ x^2 / 2 := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun y => y^2/2 - Real.log (Real.cosh y))
    (f' := fun y => y - Real.sinh y / Real.cosh y)
    (fun y _ => by
      have hsq : HasDerivAt (fun z : ℝ => z^2) (2*y) y := by
        simpa using hasDerivAt_pow 2 y
      have h2 : HasDerivAt (fun z : ℝ => z^2/2) y y := by
        have := hsq.div_const 2
        exact this.congr_deriv (by ring)
      have hlc : HasDerivAt (fun z : ℝ => Real.log (Real.cosh z))
          (Real.sinh y / Real.cosh y) y := by
        exact (Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne'
      exact h2.sub hlc)
    (by simp)
    (fun y hy => by
      have hc := Real.cosh_pos y
      rw [sub_nonneg, div_le_iff₀ hc]
      exact sinh_le_mul_cosh y hy.le)
    x hx
  linarith

/-! ### Klein–Rio Lemma 4.5 -/

/-- Klein–Rio Lemma 4.5, lower bound: `t ≤ φ(t)` for `t ≥ 0`.
(Paper proof: `φ(t) = tψ(t) + ψ(t)·log cosh t ≥ t` since `ψ ≥ 1` and
`cosh ≥ 1`; it holds for every `t ≥ 0`.) -/
theorem lemma45_lower (t : ℝ) (ht : 0 ≤ t) : t ≤ phiKR t := by
  have hψ1 : 1 ≤ psiKR t := psiKR_ge_one t ht
  have hc : 0 ≤ Real.log (Real.cosh t) := Real.log_nonneg (Real.one_le_cosh t)
  unfold phiKR
  rw [log_psiKR]
  nlinarith [mul_nonneg (sub_nonneg.mpr hψ1) ht,
    mul_nonneg (by linarith : (0:ℝ) ≤ psiKR t) hc]

/-- Klein–Rio Lemma 4.5, upper bound: `φ(t) ≤ t·e^{2t} − t²/2` for
`t ∈ [0, 1/2]`.  The paper states this for `t ∈ [0, t₀]` where `t₀ < 1/2`
is the root of `φ = 1`; the §5 argument (via `e^{−2t} ≤ 1 − t` on `[0,1/2]`,
here replaced by `log cosh t ≤ t²/2` and `1 + 2t ≤ e^{2t}`) covers all of
`[0, 1/2]`. -/
theorem lemma45_upper (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1/2) :
    phiKR t ≤ t * Real.exp (2*t) - t^2/2 := by
  have key := nonneg_of_deriv_nonneg_Icc (a := 0) (b := 1/2)
    (f := fun y => y * Real.exp (2*y) - y^2/2 - phiKR y)
    (f' := fun y => Real.exp (2*y) * (2*y - Real.log (psiKR y)) - y)
    (fun x _ => by
      have hψpos : 0 < psiKR x := psiKR_pos x
      have h2x : HasDerivAt (fun y : ℝ => 2*y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2:ℝ)
      have hexp : HasDerivAt (fun y : ℝ => Real.exp (2*y)) (Real.exp (2*x) * 2) x :=
        h2x.exp
      have hψd : HasDerivAt psiKR (Real.exp (2*x)) x := by
        have := (hexp.add_const 1).div_const 2
        unfold psiKR
        exact this.congr_deriv (by ring)
      have hlogd : HasDerivAt (fun y : ℝ => Real.log (psiKR y))
          (Real.exp (2*x) / psiKR x) x := by
        exact hψd.log hψpos.ne'
      have hφd : HasDerivAt phiKR
          (Real.exp (2*x) * Real.log (psiKR x) + psiKR x * (Real.exp (2*x) / psiKR x))
          x := hψd.mul hlogd
      have h3 : HasDerivAt (fun y : ℝ => y * Real.exp (2*y))
          (1 * Real.exp (2*x) + x * (Real.exp (2*x) * 2)) x :=
        (hasDerivAt_id x).mul hexp
      have hsq : HasDerivAt (fun z : ℝ => z^2) (2*x) x := by
        simpa using hasDerivAt_pow 2 x
      have h4 : HasDerivAt (fun y : ℝ => y^2/2) x x := by
        have := hsq.div_const 2
        exact this.congr_deriv (by ring)
      have := (h3.sub h4).sub hφd
      have hcancel : psiKR x * (Real.exp (2*x) / psiKR x) = Real.exp (2*x) := by
        field_simp
      exact this.congr_deriv (by rw [hcancel]; ring))
    (by simp [phiKR_zero])
    (fun x hx => by
      have hx0 : 0 < x := hx.1
      have hx2 : x < 1/2 := hx.2
      have hlc : Real.log (Real.cosh x) ≤ x^2/2 := log_cosh_le x hx0.le
      have hL : Real.log (psiKR x) ≤ x + x^2/2 := by
        rw [log_psiKR]; linarith
      have hE : (0:ℝ) < Real.exp (2*x) := Real.exp_pos _
      have hE1 : 1 + 2*x ≤ Real.exp (2*x) := by
        linarith [Real.add_one_le_exp (2*x)]
      have hxx : 0 ≤ x - x^2/2 := by nlinarith
      have s1 : Real.exp (2*x) * (x - x^2/2)
          ≤ Real.exp (2*x) * (2*x - Real.log (psiKR x)) :=
        mul_le_mul_of_nonneg_left (by linarith) hE.le
      have s2 : (1 + 2*x) * (x - x^2/2) ≤ Real.exp (2*x) * (x - x^2/2) :=
        mul_le_mul_of_nonneg_right hE1 hxx
      nlinarith [s1, s2, mul_nonneg (sq_nonneg x) (by linarith : (0:ℝ) ≤ 3/2 - x)])
    t (Set.mem_Icc.mpr ⟨ht0, ht⟩)
  linarith

/-! ### Klein–Rio Lemma 4.4: the monotone ratio `x ↦ x⁻²(1 + (x−1)eˣ)` -/

/-- Derivative of the numerator `N(x) = (x²−2x+2)eˣ − 2` of `gKR'`. -/
private theorem NKR_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y^2 - 2*y + 2) * Real.exp y - 2)
      (x^2 * Real.exp x) x := by
  have hsq : HasDerivAt (fun z : ℝ => z^2) (2*x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y : ℝ => 2*y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2:ℝ)
  have hp : HasDerivAt (fun y : ℝ => y^2 - 2*y + 2) (2*x - 2) x :=
    (hsq.sub h2).add_const 2
  have := (hp.mul (Real.hasDerivAt_exp x)).sub_const 2
  exact this.congr_deriv (by ring)

/-- `N ≥ 0` on `[0,∞)`. -/
private theorem NKR_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (x^2 - 2*x + 2) * Real.exp x - 2 :=
  nonneg_of_deriv_nonneg_Ici
    (f' := fun y => y^2 * Real.exp y)
    (fun y _ => NKR_hasDerivAt y)
    (by norm_num)
    (fun y _ => by positivity)
    x hx

/-- `N ≤ 0` on `(−∞,0]`. -/
private theorem NKR_nonpos (x : ℝ) (hx : x ≤ 0) :
    (x^2 - 2*x + 2) * Real.exp x - 2 ≤ 0 :=
  nonpos_of_deriv_nonneg_Iic
    (f' := fun y => y^2 * Real.exp y)
    (fun y _ => NKR_hasDerivAt y)
    (by norm_num)
    (fun y _ => by positivity)
    x hx

/-- Derivative of the bridge function `(x−1)eˣ + 1 − x²/2`. -/
private theorem bridge_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - 1) * Real.exp y + 1 - y^2/2)
      (x * (Real.exp x - 1)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - 1) * Real.exp y)
      (1 * Real.exp x + (x - 1) * Real.exp x) x :=
    ((hasDerivAt_id x).sub_const 1).mul (Real.hasDerivAt_exp x)
  have hsq : HasDerivAt (fun z : ℝ => z^2) (2*x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y : ℝ => y^2/2) x x := by
    have := hsq.div_const 2
    exact this.congr_deriv (by ring)
  have := (h1.add_const 1).sub h2
  exact this.congr_deriv (by ring)

/-- Bridge, right half: `x²/2 ≤ (x−1)eˣ + 1` for `x ≥ 0`. -/
private theorem bridge_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (x - 1) * Real.exp x + 1 - x^2/2 :=
  nonneg_of_deriv_nonneg_Ici
    (f' := fun y => y * (Real.exp y - 1))
    (fun y _ => bridge_hasDerivAt y)
    (by norm_num)
    (fun y hy => mul_nonneg hy.le (by linarith [Real.add_one_le_exp y]))
    x hx

/-- Bridge, left half: `(x−1)eˣ + 1 ≤ x²/2` for `x ≤ 0`. -/
private theorem bridge_nonpos (x : ℝ) (hx : x ≤ 0) :
    (x - 1) * Real.exp x + 1 - x^2/2 ≤ 0 :=
  nonpos_of_deriv_nonneg_Iic
    (f' := fun y => y * (Real.exp y - 1))
    (fun y _ => bridge_hasDerivAt y)
    (by norm_num)
    (fun y hy => by
      have h1 : Real.exp y < 1 := by
        have := Real.exp_lt_exp.mpr hy
        simpa using this
      exact le_of_lt (mul_pos_of_neg_of_neg hy (by linarith)))
    x hx

/-- Klein–Rio Lemma 4.4: `g(x) = x⁻²(1 + (x−1)eˣ)`, extended by continuity
with `g(0) = 1/2`. -/
noncomputable def gKR (x : ℝ) : ℝ :=
  if x = 0 then 1/2 else (1 + (x - 1) * Real.exp x) / x^2

theorem gKR_zero : gKR 0 = 1/2 := by simp [gKR]

private theorem half_le_gKR (x : ℝ) (hx : 0 ≤ x) : 1/2 ≤ gKR x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, gKR_zero]
  · have hb := bridge_nonneg x hx
    unfold gKR
    rw [if_neg (ne_of_gt h), le_div_iff₀ (by positivity)]
    linarith

private theorem gKR_le_half (x : ℝ) (hx : x ≤ 0) : gKR x ≤ 1/2 := by
  rcases hx.lt_or_eq with h | h
  · have hb := bridge_nonpos x hx
    have hx2 : (0:ℝ) < x^2 :=
      lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 (ne_of_lt h)))
    unfold gKR
    rw [if_neg (ne_of_lt h), div_le_iff₀ hx2]
    linarith
  · rw [h, gKR_zero]

/-- `gKR` is differentiable away from `0`, with derivative `N(x)/x³`. -/
private theorem gKR_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt gKR (((x^2 - 2*x + 2) * Real.exp x - 2) / x^3) x := by
  have hnum : HasDerivAt (fun y : ℝ => 1 + (y - 1) * Real.exp y)
      (1 * Real.exp x + (x - 1) * Real.exp x) x :=
    (((hasDerivAt_id x).sub_const 1).mul (Real.hasDerivAt_exp x)).const_add 1
  have hden : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
    simpa using hasDerivAt_pow 2 x
  have hx2 : x^2 ≠ 0 := pow_ne_zero 2 hx
  have hdiv := hnum.div hden hx2
  have hev : gKR =ᶠ[nhds x] fun y : ℝ => (1 + (y - 1) * Real.exp y) / y^2 := by
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr hx)] with y hy
    have hy0 : y ≠ 0 := Set.mem_compl_singleton_iff.mp hy
    simp only [gKR, if_neg hy0]
  have hg := hdiv.congr_of_eventuallyEq hev
  exact hg.congr_deriv (by field_simp <;> ring)

private theorem gKR_mono_Iio : MonotoneOn gKR (Set.Iio (0:ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iio 0)
  · intro x hx
    exact (gKR_hasDerivAt x (ne_of_lt (Set.mem_Iio.mp hx))).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iio] at hx
    exact (gKR_hasDerivAt x
      (ne_of_lt (Set.mem_Iio.mp hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Iio] at hx
    have hx' : x < 0 := Set.mem_Iio.mp hx
    rw [(gKR_hasDerivAt x (ne_of_lt hx')).deriv]
    have hN := NKR_nonpos x hx'.le
    have hx3 : x^3 < 0 := by nlinarith [mul_pos_of_neg_of_neg hx' hx']
    have hq := div_nonneg (neg_nonneg.mpr hN) (neg_nonneg.mpr hx3.le)
    rwa [neg_div_neg_eq] at hq

private theorem gKR_mono_Ioi : MonotoneOn gKR (Set.Ioi (0:ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx
    exact (gKR_hasDerivAt x (ne_of_gt (Set.mem_Ioi.mp hx))).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (gKR_hasDerivAt x
      (ne_of_gt (Set.mem_Ioi.mp hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : (0:ℝ) < x := Set.mem_Ioi.mp hx
    rw [(gKR_hasDerivAt x (ne_of_gt hx')).deriv]
    exact div_nonneg (NKR_nonneg x hx'.le) (pow_nonneg hx'.le 3)

/-- Klein–Rio Lemma 4.4 (monotone-ratio step, "from l'Hôpital's rule for
monotonicity"): `gKR` is nondecreasing on the whole real line. -/
theorem lemma44_g_mono : ∀ x x' : ℝ, x ≤ x' → gKR x ≤ gKR x' := by
  intro x x' h
  rcases lt_or_ge x 0 with hx | hx
  · rcases lt_or_ge x' 0 with hx' | hx'
    · exact gKR_mono_Iio (Set.mem_Iio.mpr hx) (Set.mem_Iio.mpr hx') h
    · exact le_trans (gKR_le_half x hx.le) (half_le_gKR x' hx')
  · rcases eq_or_lt_of_le hx with h0 | h0
    · rw [← h0, gKR_zero]
      exact half_le_gKR x' (le_trans (le_of_eq h0) h)
    · exact gKR_mono_Ioi (Set.mem_Ioi.mpr h0)
        (Set.mem_Ioi.mpr (lt_of_lt_of_le h0 h)) h

/-- Klein–Rio Lemma 4.4 (pointwise consequence): for `t > 0` and `y ≤ 1`,
`(ty − 1)e^{ty} + 1 ≤ y²(1 + (t−1)eᵗ)`. -/
theorem lemma44_consequence (t y : ℝ) (ht : 0 < t) (hy : y ≤ 1) :
    (t*y - 1) * Real.exp (t*y) + 1 ≤ y^2 * (1 + (t - 1) * Real.exp t) := by
  have hty : t*y ≤ t := by nlinarith
  have hmono := lemma44_g_mono (t*y) t hty
  by_cases h0 : t*y = 0
  · have hy0 : y = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (ne_of_gt ht)
      · exact h
    subst hy0
    norm_num
  · unfold gKR at hmono
    rw [if_neg h0, if_neg (ne_of_gt ht)] at hmono
    have h1 : (0:ℝ) < (t*y)^2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
    have h2 : (0:ℝ) < t^2 := pow_pos ht 2
    rw [div_le_div_iff₀ h1 h2] at hmono
    nlinarith [hmono, h2]

end TalagrandCore
end

/-! ## Component: KRMgf -/
section
/-
Klein–Rio machinery, part 2: per-coordinate mgf/cgf of the NEGATED linear
summand `Y_{a,x}(b) = −linSummand coeff p a x b = (p − χ b)·coeff a x`.

  krM a x t  =  E_b e^{t·Y}  =  bw(true)·e^{−t·lin(true)} + bw(false)·e^{−t·lin(false)}
  krl = log krM,   krL a = ∑_x krl a x,   with derivatives krMd/krld/krLd.

Main facts:
* `krM_pos`, `krM_one_le` (centering ⟹ mgf ≥ 1), `krl_zero`, `krl_nonneg`;
* `hasDerivAt_krM/krl/krL` with the explicit derivative;
* `krl_tderiv_sub_nonneg` : 0 ≤ t·krl′ − krl (entropy nonnegativity);
* `krl_tderiv_sub_le` (Klein–Rio Lemma 4.4, per coordinate):
    t·krl′(t) − krl(t) ≤ p(1−p)·c²·(1 + (t−1)eᵗ);
* `krL_tderiv_sub_le` : summed version against `sigmaSq`;
* `krM_le_psiKR` : E e^{tY} ≤ cosh t ≤ (e^{2t}+1)/2 for |c| ≤ 1, t ≥ 0;
* `Ex_prod_coord` (product factorization) and `log_Ex_exp_neg_linSum = krL`;
* `cgf_neg_le_linear` : log Ex e^{−εf} ≤ −ε·Ex f + ε²·Ex(f²e^{|f|}), 0 ≤ ε ≤ 1.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι]

/-! ### The product factorization of coordinatewise expectations -/

/-- Expectation of a product of per-coordinate functions factorizes. -/
theorem Ex_prod_coord (p : ℝ) (u : κ → Bool → ℝ) :
    Ex p (fun ω => ∏ x : κ, u x (ω x)) =
      ∏ x : κ, (bw p true * u x true + bw p false * u x false) := by
  unfold Ex W
  have hpt : ∀ ω : κ → Bool,
      (∏ x : κ, bw p (ω x)) * (∏ x : κ, u x (ω x)) =
        ∏ x : κ, (bw p (ω x) * u x (ω x)) := by
    intro ω; rw [← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun ω _ => hpt ω)]
  have h := Finset.prod_univ_sum (fun _ : κ => (Finset.univ : Finset Bool))
      (fun (x : κ) (b : Bool) => bw p b * u x b)
  have huniv :
      (Finset.univ : Finset (κ → Bool)) =
        Fintype.piFinset (fun _ : κ => (Finset.univ : Finset Bool)) :=
    (Fintype.piFinset_univ).symm
  rw [huniv, ← h]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp

/-! ### Definitions -/

/-- The full linear sum `S_a(ω) = ∑_x (χ(ω x) − p)·c_a(x)`. -/
noncomputable def linSum (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (ω : κ → Bool) : ℝ :=
  ∑ x : κ, linSummand coeff p a x (ω x)

/-- Per-coordinate mgf of the negated summand. -/
noncomputable def krM (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  bw p true * Real.exp (-(t * linSummand coeff p a x true)) +
    bw p false * Real.exp (-(t * linSummand coeff p a x false))

/-- Its explicit `t`-derivative. -/
noncomputable def krMd (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  bw p true * (-linSummand coeff p a x true) *
      Real.exp (-(t * linSummand coeff p a x true)) +
    bw p false * (-linSummand coeff p a x false) *
      Real.exp (-(t * linSummand coeff p a x false))

/-- Per-coordinate cgf `krl = log krM`. -/
noncomputable def krl (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  Real.log (krM coeff p a x t)

/-- Its derivative `krld = krMd / krM`. -/
noncomputable def krld (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  krMd coeff p a x t / krM coeff p a x t

/-- Branch cgf `L_a(t) = ∑_x krl a x t = log E e^{−t·S_a}`. -/
noncomputable def krL (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (t : ℝ) : ℝ :=
  ∑ x : κ, krl coeff p a x t

/-- Its derivative. -/
noncomputable def krLd (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (t : ℝ) : ℝ :=
  ∑ x : κ, krld coeff p a x t

/-! ### Two-point averages of the linear summand -/

theorem linSummand_avg (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) :
    bw p true * linSummand coeff p a x true +
      bw p false * linSummand coeff p a x false = 0 := by
  simp only [linSummand, bw]
  simp only [cond_true, cond_false]
  ring

theorem linSummand_sq_avg (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) :
    bw p true * linSummand coeff p a x true ^ 2 +
      bw p false * linSummand coeff p a x false ^ 2 =
      p * (1 - p) * coeff a x ^ 2 := by
  simp only [linSummand, bw]
  simp only [cond_true, cond_false]
  ring

theorem linSummand_abs_le {coeff : ι → κ → ℝ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {a : ι} {x : κ} (hB : |coeff a x| ≤ 1) (b : Bool) :
    |linSummand coeff p a x b| ≤ 1 := by
  have : |linSummand coeff p a x b| = |cond b (1:ℝ) 0 - p| * |coeff a x| := by
    rw [linSummand, abs_mul]
  rw [this]
  have hb : |cond b (1:ℝ) 0 - p| ≤ 1 := by
    cases b <;> simp only [cond_true, cond_false] <;> rw [abs_le] <;> constructor <;> linarith
  calc |cond b (1:ℝ) 0 - p| * |coeff a x| ≤ 1 * 1 :=
        mul_le_mul hb hB (abs_nonneg _) (by linarith)
    _ = 1 := one_mul 1

/-! ### Basic mgf facts -/

theorem krM_pos {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (a : ι) (x : κ) (t : ℝ) : 0 < krM coeff p a x t := by
  unfold krM
  have h1' := Real.exp_pos (-(t * linSummand coeff p a x true))
  have h2' := Real.exp_pos (-(t * linSummand coeff p a x false))
  have hbt := bw_nonneg h0 h1 true
  have hbf := bw_nonneg h0 h1 false
  have hsum := bw_sum p
  rcases eq_or_lt_of_le hbt with h | h
  · have hf1 : bw p false = 1 := by linarith
    have hpos := mul_pos (by linarith : (0:ℝ) < bw p false) h2'
    nlinarith [mul_nonneg hbt h1'.le]
  · have hpos := mul_pos h h1'
    nlinarith [mul_nonneg hbf h2'.le]

theorem krM_one_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (a : ι) (x : κ) (t : ℝ) : 1 ≤ krM coeff p a x t := by
  unfold krM
  have h1' := Real.add_one_le_exp (-(t * linSummand coeff p a x true))
  have h2' := Real.add_one_le_exp (-(t * linSummand coeff p a x false))
  have hbt := bw_nonneg h0 h1 true
  have hbf := bw_nonneg h0 h1 false
  have hsum := bw_sum p
  have havg := linSummand_avg coeff p a x
  have ht0 : t * (bw p true * linSummand coeff p a x true +
      bw p false * linSummand coeff p a x false) = 0 := by rw [havg]; ring
  nlinarith [mul_le_mul_of_nonneg_left h1' hbt, mul_le_mul_of_nonneg_left h2' hbf, ht0]

theorem krM_zero {p : ℝ} (coeff : ι → κ → ℝ) (a : ι) (x : κ) :
    krM coeff p a x 0 = 1 := by
  unfold krM
  simp [bw]

theorem krl_zero {p : ℝ} (coeff : ι → κ → ℝ) (a : ι) (x : κ) :
    krl coeff p a x 0 = 0 := by
  rw [krl, krM_zero, Real.log_one]

theorem krl_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (a : ι) (x : κ) (t : ℝ) : 0 ≤ krl coeff p a x t :=
  Real.log_nonneg (krM_one_le h0 h1 coeff a x t)

theorem krL_zero {p : ℝ} (coeff : ι → κ → ℝ) (a : ι) : krL coeff p a 0 = 0 := by
  unfold krL
  exact Finset.sum_eq_zero fun x _ => krl_zero coeff a x

theorem krL_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (a : ι) (t : ℝ) : 0 ≤ krL coeff p a t :=
  Finset.sum_nonneg fun x _ => krl_nonneg h0 h1 coeff a x t

/-! ### Derivatives -/

theorem hasDerivAt_krM (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) :
    HasDerivAt (krM coeff p a x) (krMd coeff p a x t) t := by
  have hbranch : ∀ A : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-(s * A)))
      (-A * Real.exp (-(t * A))) t := by
    intro A
    have hlin : HasDerivAt (fun s : ℝ => -(s * A)) (-A) t := by
      exact (((hasDerivAt_id t).mul_const A).neg).congr_deriv (by ring)
    simpa [mul_comm] using hlin.exp
  have h1 := ((hbranch (linSummand coeff p a x true)).const_mul (bw p true))
  have h2 := ((hbranch (linSummand coeff p a x false)).const_mul (bw p false))
  have := h1.add h2
  refine this.congr_deriv ?_
  unfold krMd
  ring

theorem hasDerivAt_krl {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (a : ι) (x : κ) (t : ℝ) :
    HasDerivAt (krl coeff p a x) (krld coeff p a x t) t := by
  have h := (hasDerivAt_krM coeff p a x t).log
    (ne_of_gt (krM_pos h0 h1 coeff a x t))
  exact h

theorem hasDerivAt_krL {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (a : ι) (t : ℝ) :
    HasDerivAt (krL coeff p a) (krLd coeff p a t) t := by
  unfold krL krLd
  have h := HasDerivAt.sum
    (fun x (_ : x ∈ (Finset.univ : Finset κ)) => hasDerivAt_krl h0 h1 coeff a x t)
  have hfun : (∑ x : κ, krl coeff p a x) = fun s : ℝ => ∑ x : κ, krl coeff p a x s := by
    funext s
    exact Finset.sum_apply s Finset.univ _
  rw [hfun] at h
  exact h

/-! ### Two-point entropy nonnegativity -/

/-- Two-point Jensen for `x log x`, proved from `log y ≥ 1 − 1/y`. -/
theorem two_point_xlogx {w1 w2 T1 T2 : ℝ} (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (hsum : w1 + w2 = 1) (hT1 : 0 < T1) (hT2 : 0 < T2) :
    (w1 * T1 + w2 * T2) * Real.log (w1 * T1 + w2 * T2) ≤
      w1 * (T1 * Real.log T1) + w2 * (T2 * Real.log T2) := by
  set m := w1 * T1 + w2 * T2 with hm
  have hmpos : 0 < m := by
    rcases le_total w1 (1/2) with h | h
    · have hw2' : (0:ℝ) < w2 := by linarith
      have : 0 < w2 * T2 := mul_pos hw2' hT2
      nlinarith [mul_nonneg hw1 hT1.le]
    · have : 0 < w1 * T1 := mul_pos (by linarith) hT1
      nlinarith [mul_nonneg hw2 hT2.le]
  -- log(m/T_i) ≤ m/T_i − 1, multiplied by w_i T_i ≥ 0 and summed.
  have key : ∀ T : ℝ, 0 < T → T * Real.log m ≤ T * Real.log T + m - T := by
    intro T hT
    have hlog := Real.log_le_sub_one_of_pos (div_pos hmpos hT)
    rw [Real.log_div (ne_of_gt hmpos) (ne_of_gt hT)] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hT.le
    have hfield : T * (m / T - 1) = m - T := by field_simp
    nlinarith [hmul, hfield]
  have k1 := mul_le_mul_of_nonneg_left (key T1 hT1) hw1
  have k2 := mul_le_mul_of_nonneg_left (key T2 hT2) hw2
  nlinarith [k1, k2]

/-- `0 ≤ t·krMd − krM·log krM` (two-point entropy nonnegativity for `e^{tY}`). -/
theorem krM_entropy_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (a : ι) (x : κ) (t : ℝ) :
    krM coeff p a x t * Real.log (krM coeff p a x t) ≤ t * krMd coeff p a x t := by
  have h2p := two_point_xlogx (bw_nonneg h0 h1 true) (bw_nonneg h0 h1 false)
    (bw_sum p) (Real.exp_pos (-(t * linSummand coeff p a x true)))
    (Real.exp_pos (-(t * linSummand coeff p a x false)))
  unfold krM krMd
  have e1 : Real.exp (-(t * linSummand coeff p a x true)) *
      Real.log (Real.exp (-(t * linSummand coeff p a x true))) =
      Real.exp (-(t * linSummand coeff p a x true)) *
        (-(t * linSummand coeff p a x true)) := by rw [Real.log_exp]
  have e2 : Real.exp (-(t * linSummand coeff p a x false)) *
      Real.log (Real.exp (-(t * linSummand coeff p a x false))) =
      Real.exp (-(t * linSummand coeff p a x false)) *
        (-(t * linSummand coeff p a x false)) := by rw [Real.log_exp]
  rw [e1, e2] at h2p
  nlinarith [h2p]

theorem krl_tderiv_sub_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (coeff : ι → κ → ℝ) (a : ι) (x : κ) (t : ℝ) :
    0 ≤ t * krld coeff p a x t - krl coeff p a x t := by
  have hM := krM_pos h0 h1 coeff a x t
  have hent := krM_entropy_nonneg h0 h1 coeff a x t
  unfold krld krl
  have hlog : Real.log (krM coeff p a x t) ≤
      t * (krMd coeff p a x t / krM coeff p a x t) := by
    rw [mul_div_assoc', le_div_iff₀ hM]
    nlinarith [hent]
  linarith

theorem krL_tderiv_sub_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (coeff : ι → κ → ℝ) (a : ι) (t : ℝ) :
    0 ≤ t * krLd coeff p a t - krL coeff p a t := by
  unfold krLd krL
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_nonneg fun x _ => krl_tderiv_sub_nonneg h0 h1 coeff a x t

/-! ### Klein–Rio Lemma 4.4, per coordinate -/

/-- `1 + (t−1)eᵗ ≥ 0` for `t ≥ 0` (via `gKR` monotonicity). -/
theorem one_add_mul_exp_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 1 + (t - 1) * Real.exp t := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h]; simp
  · have hg := lemma44_g_mono 0 t ht
    rw [gKR_zero] at hg
    have hgt : gKR t = (1 + (t - 1) * Real.exp t) / t ^ 2 := by
      rw [gKR, if_neg (ne_of_gt h)]
    rw [hgt] at hg
    have ht2 : (0:ℝ) < t ^ 2 := by positivity
    have hmul := (le_div_iff₀ ht2).mp hg
    nlinarith [hmul, ht2]

/-- Klein–Rio Lemma 4.4, per coordinate:
`t·krl′(t) − krl(t) ≤ p(1−p)·c²·(1 + (t−1)eᵗ)` for `t > 0`, `|c| ≤ 1`. -/
theorem krl_tderiv_sub_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {coeff : ι → κ → ℝ} {a : ι} {x : κ} (hB : |coeff a x| ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    t * krld coeff p a x t - krl coeff p a x t ≤
      p * (1 - p) * coeff a x ^ 2 * (1 + (t - 1) * Real.exp t) := by
  have hM := krM_pos h0 h1 coeff a x t
  have hM1 := krM_one_le h0 h1 coeff a x t
  -- Step 1: t·krld − krl ≤ t·krMd − krM·log krM  (divide by krM ≥ 1).
  have hnum : krM coeff p a x t * Real.log (krM coeff p a x t) ≤
      t * krMd coeff p a x t := krM_entropy_nonneg h0 h1 coeff a x t
  have step1 : t * krld coeff p a x t - krl coeff p a x t ≤
      t * krMd coeff p a x t - krM coeff p a x t * Real.log (krM coeff p a x t) := by
    unfold krld krl
    set M := krM coeff p a x t with hMdef
    set D := krMd coeff p a x t with hDdef
    have hMne : M ≠ 0 := ne_of_gt hM
    have hnn : 0 ≤ t * D - M * Real.log M := by linarith [hnum]
    have key : t * (D / M) - Real.log M = (t * D - M * Real.log M) / M := by
      rw [sub_div, mul_div_assoc, mul_div_cancel_left₀ _ hMne]
    rw [key]
    calc (t * D - M * Real.log M) / M ≤ (t * D - M * Real.log M) / 1 :=
          div_le_div_of_nonneg_left hnn one_pos hM1
      _ = t * D - M * Real.log M := by rw [div_one]
  -- Step 2: t·krMd − krM·log krM ≤ E((tY−1)e^{tY} + 1)  (from x log x ≥ x − 1).
  have hxlx : krM coeff p a x t - 1 ≤
      krM coeff p a x t * Real.log (krM coeff p a x t) := by
    have hinv : 0 < (krM coeff p a x t)⁻¹ := inv_pos.mpr hM
    have hlog := Real.log_le_sub_one_of_pos hinv
    rw [Real.log_inv] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hM.le
    have hMM : krM coeff p a x t * (krM coeff p a x t)⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hM)
    nlinarith [hmul, hMM]
  -- Step 3: pointwise (tY−1)e^{tY} + 1 ≤ Y²(1+(t−1)eᵗ) per branch (Lemma 4.4 core).
  have hcore : ∀ b : Bool,
      (t * (-linSummand coeff p a x b) - 1) *
          Real.exp (t * (-linSummand coeff p a x b)) + 1 ≤
        linSummand coeff p a x b ^ 2 * (1 + (t - 1) * Real.exp t) := by
    intro b
    have habs := linSummand_abs_le h0 h1 hB b
    have hy : -linSummand coeff p a x b ≤ 1 := by
      have := abs_le.mp habs; linarith [this.1]
    have := lemma44_consequence t (-linSummand coeff p a x b) ht hy
    calc (t * (-linSummand coeff p a x b) - 1) *
          Real.exp (t * (-linSummand coeff p a x b)) + 1 ≤
        (-linSummand coeff p a x b) ^ 2 * (1 + (t - 1) * Real.exp t) := this
      _ = linSummand coeff p a x b ^ 2 * (1 + (t - 1) * Real.exp t) := by ring
  -- Assemble: average hcore with weights bw, use step1 + step2.
  have hct := hcore true
  have hcf := hcore false
  have hbt := bw_nonneg h0 h1 true
  have hbf := bw_nonneg h0 h1 false
  have hsum := bw_sum p
  have hsq := linSummand_sq_avg coeff p a x
  have havgcore :
      bw p true * ((t * (-linSummand coeff p a x true) - 1) *
          Real.exp (t * (-linSummand coeff p a x true)) + 1) +
        bw p false * ((t * (-linSummand coeff p a x false) - 1) *
          Real.exp (t * (-linSummand coeff p a x false)) + 1) ≤
      p * (1 - p) * coeff a x ^ 2 * (1 + (t - 1) * Real.exp t) := by
    have m1 := mul_le_mul_of_nonneg_left hct hbt
    have m2 := mul_le_mul_of_nonneg_left hcf hbf
    have hkey : (bw p true * linSummand coeff p a x true ^ 2 +
        bw p false * linSummand coeff p a x false ^ 2) *
        (1 + (t - 1) * Real.exp t) =
        p * (1 - p) * coeff a x ^ 2 * (1 + (t - 1) * Real.exp t) := by
      rw [hsq]
    linarith [m1, m2, hkey]
  -- LHS of havgcore equals t·krMd − krM + 1.
  have hexpand :
      bw p true * ((t * (-linSummand coeff p a x true) - 1) *
          Real.exp (t * (-linSummand coeff p a x true)) + 1) +
        bw p false * ((t * (-linSummand coeff p a x false) - 1) *
          Real.exp (t * (-linSummand coeff p a x false)) + 1) =
      t * krMd coeff p a x t - krM coeff p a x t + 1 := by
    unfold krMd krM
    have et : Real.exp (t * (-linSummand coeff p a x true)) =
        Real.exp (-(t * linSummand coeff p a x true)) := by congr 1; ring
    have ef : Real.exp (t * (-linSummand coeff p a x false)) =
        Real.exp (-(t * linSummand coeff p a x false)) := by congr 1; ring
    rw [et, ef]
    linear_combination bw_sum p
  rw [hexpand] at havgcore
  linarith [step1, hxlx, havgcore]

/-- Klein–Rio (4.20): the summed version. -/
theorem krL_tderiv_sub_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {coeff : ι → κ → ℝ} {a : ι} (hB : ∀ x, |coeff a x| ≤ 1)
    {sigmaSq : ℝ} (hVar : ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq)
    {t : ℝ} (ht : 0 < t) :
    t * krLd coeff p a t - krL coeff p a t ≤
      sigmaSq * (1 + (t - 1) * Real.exp t) := by
  unfold krLd krL
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hfac := one_add_mul_exp_nonneg ht.le
  calc ∑ x : κ, (t * krld coeff p a x t - krl coeff p a x t) ≤
      ∑ x : κ, p * (1 - p) * coeff a x ^ 2 * (1 + (t - 1) * Real.exp t) :=
        Finset.sum_le_sum fun x _ => krl_tderiv_sub_le h0 h1 (hB x) ht
    _ = (∑ x : κ, p * (1 - p) * coeff a x ^ 2) * (1 + (t - 1) * Real.exp t) := by
        rw [Finset.sum_mul]
    _ ≤ sigmaSq * (1 + (t - 1) * Real.exp t) :=
        mul_le_mul_of_nonneg_right hVar hfac

/-! ### The cosh bound (for Lemma 4.2) -/

/-- `E e^{tY} ≤ cosh t` for the centered `|Y| ≤ 1` two-point variable (any `t`). -/
theorem krM_le_cosh {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {coeff : ι → κ → ℝ} {a : ι} {x : κ} (hB : |coeff a x| ≤ 1) (t : ℝ) :
    krM coeff p a x t ≤ (Real.exp t + Real.exp (-t)) / 2 := by
  -- e^{ty} ≤ cosh t + y·sinh t for |y| ≤ 1, via convexity of exp.
  have hbranch : ∀ b : Bool,
      Real.exp (-(t * linSummand coeff p a x b)) ≤
        (Real.exp t + Real.exp (-t)) / 2 +
          (-linSummand coeff p a x b) * ((Real.exp t - Real.exp (-t)) / 2) := by
    intro b
    set y := -linSummand coeff p a x b with hy
    have habs := linSummand_abs_le h0 h1 hB b
    have hy1 : -1 ≤ y := by have := abs_le.mp habs; simp only [hy]; linarith [this.2]
    have hy2 : y ≤ 1 := by have := abs_le.mp habs; simp only [hy]; linarith [this.1]
    have hconv := convexOn_exp.2 (Set.mem_univ t) (Set.mem_univ (-t))
      (by linarith : (0:ℝ) ≤ (1 + y)/2) (by linarith : (0:ℝ) ≤ (1 - y)/2)
      (by ring : (1 + y)/2 + (1 - y)/2 = 1)
    have harg : ((1 + y) / 2) • t + ((1 - y) / 2) • (-t) = t * y := by
      simp only [smul_eq_mul]; ring
    rw [harg] at hconv
    simp only [smul_eq_mul] at hconv
    have hexp : Real.exp (-(t * linSummand coeff p a x b)) = Real.exp (t * y) := by
      rw [hy]; ring_nf
    rw [hexp]
    calc Real.exp (t * y) ≤ (1 + y)/2 * Real.exp t + (1 - y)/2 * Real.exp (-t) :=
          hconv
      _ = (Real.exp t + Real.exp (-t)) / 2 +
            y * ((Real.exp t - Real.exp (-t)) / 2) := by ring
  have hbt := bw_nonneg h0 h1 true
  have hbf := bw_nonneg h0 h1 false
  have hsum := bw_sum p
  have havg := linSummand_avg coeff p a x
  have m1 := mul_le_mul_of_nonneg_left (hbranch true) hbt
  have m2 := mul_le_mul_of_nonneg_left (hbranch false) hbf
  -- weighted sum: krM ≤ cosh t + 0 = cosh t ≤ ψKR t
  have hcosh : krM coeff p a x t ≤ (Real.exp t + Real.exp (-t)) / 2 := by
    unfold krM
    have hzero : bw p true * (-linSummand coeff p a x true) +
        bw p false * (-linSummand coeff p a x false) = 0 := by linarith [havg]
    have hcollapse : bw p true * ((Real.exp t + Real.exp (-t)) / 2 +
          (-linSummand coeff p a x true) * ((Real.exp t - Real.exp (-t)) / 2)) +
        bw p false * ((Real.exp t + Real.exp (-t)) / 2 +
          (-linSummand coeff p a x false) * ((Real.exp t - Real.exp (-t)) / 2)) =
        (Real.exp t + Real.exp (-t)) / 2 := by
      linear_combination ((Real.exp t + Real.exp (-t)) / 2) * hsum +
        ((Real.exp t - Real.exp (-t)) / 2) * hzero
    linarith [add_le_add m1 m2, hcollapse]
  exact hcosh

/-- `E e^{tY} ≤ ψKR(t) = (e^{2t}+1)/2` for `t ≥ 0`. -/
theorem krM_le_psiKR {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {coeff : ι → κ → ℝ} {a : ι} {x : κ} (hB : |coeff a x| ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    krM coeff p a x t ≤ (Real.exp (2 * t) + 1) / 2 := by
  have hpsi : (Real.exp t + Real.exp (-t)) / 2 ≤ (Real.exp (2 * t) + 1) / 2 := by
    have := cosh_le_psiKR t ht
    rw [Real.cosh_eq] at this
    linarith
  linarith [krM_le_cosh h0 h1 hB t]

/-! ### The mgf factorization -/

theorem Ex_exp_neg_linSum (p : ℝ) (coeff : ι → κ → ℝ) (a : ι) (t : ℝ) :
    Ex p (fun ω => Real.exp (-(t * linSum coeff p a ω))) =
      ∏ x : κ, krM coeff p a x t := by
  have hpt : ∀ ω : κ → Bool, Real.exp (-(t * linSum coeff p a ω)) =
      ∏ x : κ, Real.exp (-(t * linSummand coeff p a x (ω x))) := by
    intro ω
    rw [← Real.exp_sum]
    congr 1
    rw [linSum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Ex_congr hpt]
  exact Ex_prod_coord p (fun x b => Real.exp (-(t * linSummand coeff p a x b)))

theorem log_Ex_exp_neg_linSum {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (coeff : ι → κ → ℝ) (a : ι) (t : ℝ) :
    Real.log (Ex p (fun ω => Real.exp (-(t * linSum coeff p a ω)))) =
      krL coeff p a t := by
  rw [Ex_exp_neg_linSum, krL]
  rw [Real.log_prod]
  · rfl
  · exact fun x _ => ne_of_gt (krM_pos h0 h1 coeff a x t)

/-! ### Crude quadratic cgf bound near 0 (for the ε → 0 limit) -/

/-- `e^u − u − 1 ≤ u²·e^{|u|}` for all real `u`. -/
theorem exp_sub_le_sq_mul_exp_abs (u : ℝ) :
    Real.exp u - u - 1 ≤ u ^ 2 * Real.exp |u| := by
  rcases le_total 0 u with h | h
  · -- u ≥ 0 : e^u − u − 1 ≤ u²/2·e^u ≤ u²e^u; prove e^u − u − 1 ≤ u²e^u directly
    rw [abs_of_nonneg h]
    have key : ∀ v : ℝ, 0 ≤ v → Real.exp v - v - 1 ≤ v ^ 2 * Real.exp v := by
      intro v hv
      have hmain := nonneg_of_deriv_nonneg_Ici
        (f := fun s => s ^ 2 * Real.exp s - (Real.exp s - s - 1))
        (f' := fun s => 2 * s * Real.exp s + s ^ 2 * Real.exp s - Real.exp s + 1)
        (fun s _hs => by
          have h1 : HasDerivAt (fun s : ℝ => s ^ 2 * Real.exp s)
              (2 * s * Real.exp s + s ^ 2 * Real.exp s) s := by
            have := (hasDerivAt_pow 2 s).mul (Real.hasDerivAt_exp s)
            exact this.congr_deriv (by ring)
          have h2 : HasDerivAt (fun s : ℝ => Real.exp s - s - 1)
              (Real.exp s - 1) s := by
            simpa using ((Real.hasDerivAt_exp s).sub (hasDerivAt_id s)).sub_const 1
          have hsub := h1.sub h2
          exact hsub.congr_deriv (by ring))
        (by norm_num)
        (fun s hs => by
          have he : 1 - s ≤ Real.exp (-s) := by
            have := Real.add_one_le_exp (-s); linarith
          have hep : 0 < Real.exp s := Real.exp_pos s
          have hprod : (1 - s) * Real.exp s ≤ 1 := by
            have := mul_le_mul_of_nonneg_right he hep.le
            rw [← Real.exp_add] at this
            simpa using this
          nlinarith [sq_nonneg s, mul_pos hs hep])
      linarith [hmain v hv]
    exact key u h
  · -- u < 0 : e^u − u − 1 ≤ u²/2 ≤ u²·e^{|u|}
    have h2 : Real.exp u - u - 1 ≤ u ^ 2 / 2 := by
      have hmain := nonpos_of_deriv_nonneg_Iic
        (f := fun s => (Real.exp s - s - 1) - s ^ 2 / 2)
        (f' := fun s => Real.exp s - 1 - s)
        (fun s _hs => by
          have h1 : HasDerivAt (fun s : ℝ => Real.exp s - s - 1)
              (Real.exp s - 1) s := by
            simpa using ((Real.hasDerivAt_exp s).sub (hasDerivAt_id s)).sub_const 1
          have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s := by
            have := (hasDerivAt_pow 2 s).div_const 2
            exact this.congr_deriv (by ring)
          have hsub := h1.sub h2
          exact hsub.congr_deriv (by ring))
        (by norm_num)
        (fun s _hs => by
          have hlin := Real.add_one_le_exp s
          linarith)
      have := hmain u h
      linarith
    have h3 : u ^ 2 / 2 ≤ u ^ 2 * Real.exp |u| := by
      have : (1:ℝ) ≤ Real.exp |u| := by
        rw [Real.one_le_exp_iff]; positivity
      nlinarith [sq_nonneg u]
    linarith

/-- Crude linear cgf bound: `log Ex e^{−εf} ≤ −ε·Ex f + ε²·Ex(f²e^{|f|})`
for `0 ≤ ε ≤ 1`. -/
theorem cgf_neg_le_linear {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (f : (κ → Bool) → ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.log (Ex p (fun ω => Real.exp (-(ε * f ω)))) ≤
      -(ε * Ex p f) + ε ^ 2 * Ex p (fun ω => f ω ^ 2 * Real.exp |f ω|) := by
  have hpt : ∀ ω, Real.exp (-(ε * f ω)) ≤
      1 - ε * f ω + ε ^ 2 * (f ω ^ 2 * Real.exp |f ω|) := by
    intro ω
    have h := exp_sub_le_sq_mul_exp_abs (-(ε * f ω))
    have habs : |(-(ε * f ω))| ≤ |f ω| := by
      rw [abs_neg, abs_mul]
      calc |ε| * |f ω| ≤ 1 * |f ω| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            rw [abs_of_nonneg hε0]; exact hε1
        _ = |f ω| := one_mul _
    have hmono : Real.exp |(-(ε * f ω))| ≤ Real.exp |f ω| := Real.exp_le_exp.mpr habs
    have hsq : (-(ε * f ω)) ^ 2 = ε ^ 2 * f ω ^ 2 := by ring
    nlinarith [h, hmono, sq_nonneg (ε * f ω), Real.exp_pos |f ω|,
      mul_le_mul_of_nonneg_left hmono (sq_nonneg (ε * f ω))]
  have hEx : Ex p (fun ω => Real.exp (-(ε * f ω))) ≤
      1 - ε * Ex p f + ε ^ 2 * Ex p (fun ω => f ω ^ 2 * Real.exp |f ω|) := by
    have := Ex_mono h0 h1 hpt
    have hsplit : Ex p (fun ω => 1 - ε * f ω + ε ^ 2 * (f ω ^ 2 * Real.exp |f ω|)) =
        1 - ε * Ex p f + ε ^ 2 * Ex p (fun ω => f ω ^ 2 * Real.exp |f ω|) := by
      rw [show (fun ω => 1 - ε * f ω + ε ^ 2 * (f ω ^ 2 * Real.exp |f ω|)) =
          (fun ω => (1 + (-ε) * f ω) + ε ^ 2 * (f ω ^ 2 * Real.exp |f ω|)) from
          funext fun ω => by ring]
      rw [Ex_add, Ex_add, Ex_const h0 h1, Ex_smul, Ex_smul]
      ring
    linarith [hsplit ▸ this]
  have hpos : 0 < Ex p (fun ω => Real.exp (-(ε * f ω))) :=
    Ex_pos h0 h1 fun ω => Real.exp_pos _
  calc Real.log (Ex p (fun ω => Real.exp (-(ε * f ω)))) ≤
      Ex p (fun ω => Real.exp (-(ε * f ω))) - 1 :=
        Real.log_le_sub_one_of_pos hpos
    _ ≤ -(ε * Ex p f) + ε ^ 2 * Ex p (fun ω => f ω ^ 2 * Real.exp |f ω|) := by
        linarith [hEx]

end TalagrandCore
end

/-! ## Component: Truncation -/
section
/-
Truncation of the linear summand at level θ: small/big parts, truncated
process trZ, remainder trW, truncated coefficient increments trC, and the
shift trShift, with the sandwich and transfer lemmas.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-! ### Definitions -/

noncomputable def trSmall (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) (x : κ) (b : Bool) : ℝ :=
  if |linSummand coeff p a x b| ≤ θ then linSummand coeff p a x b else 0

noncomputable def trBig (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) (x : κ) (b : Bool) : ℝ :=
  linSummand coeff p a x b - trSmall coeff p θ a x b

noncomputable def trZ (coeff : ι → κ → ℝ) (p θ : ℝ) (ω : κ → Bool) : ℝ :=
  supProc (trSmall coeff p θ) ω

noncomputable def trW (coeff : ι → κ → ℝ) (p θ : ℝ) (ω : κ → Bool) : ℝ :=
  supProc (fun a x b => |trBig coeff p θ a x b|) ω

noncomputable def trC (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) (x : κ) : ℝ :=
  trSmall coeff p θ a x true - trSmall coeff p θ a x false

noncomputable def trShift (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) : ℝ :=
  ∑ x : κ, (bw p true * trSmall coeff p θ a x true + bw p false * trSmall coeff p θ a x false)

/-! ### Basic facts about the big part -/

theorem trBig_eq (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) (x : κ) (b : Bool) :
    trBig coeff p θ a x b =
      if |linSummand coeff p a x b| ≤ θ then 0 else linSummand coeff p a x b := by
  unfold trBig trSmall
  split <;> ring

theorem abs_trBig_nonneg (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) (x : κ) (b : Bool) :
    0 ≤ |trBig coeff p θ a x b| := abs_nonneg _

theorem abs_trBig_le_one {coeff : ι → κ → ℝ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hB : ∀ a x, |coeff a x| ≤ 1) (θ : ℝ) (a : ι) (x : κ) (b : Bool) :
    |trBig coeff p θ a x b| ≤ 1 := by
  rw [trBig_eq]
  split
  · simp
  · exact linSummand_abs_le h0 h1 (hB a x) b

theorem abs_trBig_le_sq_div {θ : ℝ} (hθ : 0 < θ) (coeff : ι → κ → ℝ) (p : ℝ)
    (a : ι) (x : κ) (b : Bool) :
    |trBig coeff p θ a x b| ≤ linSummand coeff p a x b ^ 2 / θ := by
  rw [trBig_eq]
  split_ifs with h
  · simp only [abs_zero]
    positivity
  · rw [le_div_iff₀ hθ]
    have h2 : θ ≤ |linSummand coeff p a x b| := le_of_lt (not_le.mp h)
    nlinarith [abs_nonneg (linSummand coeff p a x b), sq_abs (linSummand coeff p a x b)]

/-! ### Sandwiching Zproc between trZ and trW -/

theorem Zproc_le_trZ_add_trW (coeff : ι → κ → ℝ) (p θ : ℝ) (ω : κ → Bool) :
    Zproc coeff p ω ≤ trZ coeff p θ ω + trW coeff p θ ω := by
  unfold Zproc supProc
  apply Finset.sup'_le
  intro a _
  calc ∑ x : κ, linSummand coeff p a x (ω x)
      = ∑ x : κ, (trSmall coeff p θ a x (ω x) + trBig coeff p θ a x (ω x)) :=
        Finset.sum_congr rfl fun x _ => by unfold trBig; ring
    _ = (∑ x : κ, trSmall coeff p θ a x (ω x)) + ∑ x : κ, trBig coeff p θ a x (ω x) :=
        Finset.sum_add_distrib
    _ ≤ (∑ x : κ, trSmall coeff p θ a x (ω x)) + ∑ x : κ, |trBig coeff p θ a x (ω x)| :=
        add_le_add le_rfl (Finset.sum_le_sum fun x _ => le_abs_self _)
    _ ≤ trZ coeff p θ ω + trW coeff p θ ω :=
        add_le_add (le_supProc _ ω a)
          (le_supProc (fun a x b => |trBig coeff p θ a x b|) ω a)

theorem trZ_le_Zproc_add_trW (coeff : ι → κ → ℝ) (p θ : ℝ) (ω : κ → Bool) :
    trZ coeff p θ ω ≤ Zproc coeff p ω + trW coeff p θ ω := by
  unfold trZ supProc
  apply Finset.sup'_le
  intro a _
  have hterm : ∀ x : κ, trSmall coeff p θ a x (ω x) ≤
      linSummand coeff p a x (ω x) + |trBig coeff p θ a x (ω x)| := by
    intro x
    have h1 : -trBig coeff p θ a x (ω x) ≤ |trBig coeff p θ a x (ω x)| := neg_le_abs _
    have h2 : trSmall coeff p θ a x (ω x) =
        linSummand coeff p a x (ω x) - trBig coeff p θ a x (ω x) := by
      unfold trBig; ring
    linarith
  calc ∑ x : κ, trSmall coeff p θ a x (ω x)
      ≤ ∑ x : κ, (linSummand coeff p a x (ω x) + |trBig coeff p θ a x (ω x)|) :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = (∑ x : κ, linSummand coeff p a x (ω x)) + ∑ x : κ, |trBig coeff p θ a x (ω x)| :=
        Finset.sum_add_distrib
    _ ≤ Zproc coeff p ω + trW coeff p θ ω :=
        add_le_add (le_supProc _ ω a)
          (le_supProc (fun a x b => |trBig coeff p θ a x b|) ω a)

/-! ### Bounding trW by the variance process -/

theorem trW_le_Sigma2_div {θ : ℝ} (hθ : 0 < θ) (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) :
    trW coeff p θ ω ≤ Sigma2 coeff p ω / θ := by
  unfold trW supProc
  apply Finset.sup'_le
  intro a _
  have hstep : ∀ x : κ, |trBig coeff p θ a x (ω x)| ≤
      coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - p) ^ 2 / θ := by
    intro x
    refine le_trans (abs_trBig_le_sq_div hθ coeff p a x (ω x)) ?_
    have h : linSummand coeff p a x (ω x) ^ 2 =
        coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - p) ^ 2 := by
      unfold linSummand; ring
    rw [h]
  calc ∑ x : κ, |trBig coeff p θ a x (ω x)|
      ≤ ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - p) ^ 2 / θ :=
        Finset.sum_le_sum fun x _ => hstep x
    _ = (∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - p) ^ 2) / θ :=
        (Finset.sum_div _ _ _).symm
    _ ≤ Sigma2 coeff p ω / θ := by
        gcongr
        exact Finset.le_sup'
          (f := fun a : ι => ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - p) ^ 2)
          (Finset.mem_univ a)

theorem Ex_trW_le {p θ : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ : 0 < θ) (coeff : ι → κ → ℝ) :
    Ex p (trW coeff p θ) ≤ Ex p (Sigma2 coeff p) / θ := by
  have hmono : Ex p (trW coeff p θ) ≤ Ex p (fun ω => Sigma2 coeff p ω / θ) :=
    Ex_mono h0 h1 fun ω => trW_le_Sigma2_div hθ coeff p ω
  have heq : Ex p (fun ω => Sigma2 coeff p ω / θ) = Ex p (Sigma2 coeff p) / θ := by
    have h : ∀ ω : κ → Bool, Sigma2 coeff p ω / θ = θ⁻¹ * Sigma2 coeff p ω := by
      intro ω; rw [inv_mul_eq_div]
    rw [Ex_congr h, Ex_smul, inv_mul_eq_div]
  linarith

/-! ### The affine identity and bounds on trC -/

theorem trSmall_affine {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ) (θ : ℝ)
    (a : ι) (x : κ) (b : Bool) :
    trSmall coeff p θ a x b =
      (bw p true * trSmall coeff p θ a x true + bw p false * trSmall coeff p θ a x false) +
        (cond b (1:ℝ) 0 - p) * trC coeff p θ a x := by
  unfold trC
  cases b <;> simp only [bw, cond_true, cond_false] <;> ring

theorem abs_trC_le_coeff {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ) (θ : ℝ)
    (a : ι) (x : κ) : |trC coeff p θ a x| ≤ |coeff a x| := by
  have hT : linSummand coeff p a x true = (1 - p) * coeff a x := by
    simp [linSummand]
  have hF : linSummand coeff p a x false = (0 - p) * coeff a x := by
    simp [linSummand]
  unfold trC trSmall
  split_ifs
  · rw [hT, hF]
    have h : (1 - p) * coeff a x - (0 - p) * coeff a x = coeff a x := by ring
    rw [h]
  · rw [sub_zero, hT, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - p)]
    nlinarith [abs_nonneg (coeff a x)]
  · rw [zero_sub, abs_neg, hF, abs_mul]
    have h : |0 - p| = p := by rw [abs_of_nonpos (by linarith)]; ring
    rw [h]
    nlinarith [abs_nonneg (coeff a x)]
  · simp

theorem abs_trSmall_le {θ : ℝ} (hθ0 : 0 ≤ θ) (coeff : ι → κ → ℝ) (p : ℝ)
    (a : ι) (x : κ) (b : Bool) : |trSmall coeff p θ a x b| ≤ θ := by
  unfold trSmall
  split_ifs with h
  · exact h
  · simpa using hθ0

theorem abs_trC_le_two_theta {θ : ℝ} (hθ0 : 0 ≤ θ) (coeff : ι → κ → ℝ) (p : ℝ)
    (a : ι) (x : κ) : |trC coeff p θ a x| ≤ 2 * θ := by
  unfold trC
  have habs : |trSmall coeff p θ a x true - trSmall coeff p θ a x false| ≤
      |trSmall coeff p θ a x true| + |trSmall coeff p θ a x false| := by
    calc |trSmall coeff p θ a x true - trSmall coeff p θ a x false|
        = |trSmall coeff p θ a x true + -trSmall coeff p θ a x false| := by
          rw [sub_eq_add_neg]
      _ ≤ |trSmall coeff p θ a x true| + |-trSmall coeff p θ a x false| := abs_add_le _ _
      _ = |trSmall coeff p θ a x true| + |trSmall coeff p θ a x false| := by rw [abs_neg]
  have h1 := abs_trSmall_le hθ0 coeff p a x true
  have h2 := abs_trSmall_le hθ0 coeff p a x false
  linarith

/-! ### Bounding the shift -/

theorem abs_shift_summand_le {p θ : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ : 0 < θ)
    (coeff : ι → κ → ℝ) (a : ι) (x : κ) :
    |bw p true * trSmall coeff p θ a x true + bw p false * trSmall coeff p θ a x false| ≤
      p * (1 - p) * coeff a x ^ 2 / θ := by
  have hs : ∀ b, trSmall coeff p θ a x b =
      linSummand coeff p a x b - trBig coeff p θ a x b := by
    intro b; unfold trBig; ring
  have havg := linSummand_avg coeff p a x
  have hkey : bw p true * trSmall coeff p θ a x true +
      bw p false * trSmall coeff p θ a x false =
      -(bw p true * trBig coeff p θ a x true + bw p false * trBig coeff p θ a x false) := by
    rw [hs true, hs false]
    linear_combination havg
  rw [hkey, abs_neg]
  have hbT := bw_nonneg h0 h1 true
  have hbF := bw_nonneg h0 h1 false
  have htri : |bw p true * trBig coeff p θ a x true +
      bw p false * trBig coeff p θ a x false| ≤
      bw p true * |trBig coeff p θ a x true| + bw p false * |trBig coeff p θ a x false| := by
    calc |bw p true * trBig coeff p θ a x true + bw p false * trBig coeff p θ a x false|
        ≤ |bw p true * trBig coeff p θ a x true| + |bw p false * trBig coeff p θ a x false| :=
          abs_add_le _ _
      _ = bw p true * |trBig coeff p θ a x true| + bw p false * |trBig coeff p θ a x false| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hbT, abs_of_nonneg hbF]
  have hb3T : bw p true * |trBig coeff p θ a x true| ≤
      bw p true * (linSummand coeff p a x true ^ 2 / θ) :=
    mul_le_mul_of_nonneg_left (abs_trBig_le_sq_div hθ coeff p a x true) hbT
  have hb3F : bw p false * |trBig coeff p θ a x false| ≤
      bw p false * (linSummand coeff p a x false ^ 2 / θ) :=
    mul_le_mul_of_nonneg_left (abs_trBig_le_sq_div hθ coeff p a x false) hbF
  have hsq := linSummand_sq_avg coeff p a x
  have heq : bw p true * (linSummand coeff p a x true ^ 2 / θ) +
      bw p false * (linSummand coeff p a x false ^ 2 / θ) =
      p * (1 - p) * coeff a x ^ 2 / θ := by
    rw [← hsq]; ring
  linarith

theorem abs_trShift_le {p θ sigmaSq : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ : 0 < θ)
    (coeff : ι → κ → ℝ) (a : ι)
    (hVar : ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq) :
    |trShift coeff p θ a| ≤ sigmaSq / θ := by
  unfold trShift
  calc |∑ x : κ, (bw p true * trSmall coeff p θ a x true +
        bw p false * trSmall coeff p θ a x false)|
      ≤ ∑ x : κ, |bw p true * trSmall coeff p θ a x true +
          bw p false * trSmall coeff p θ a x false| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : κ, p * (1 - p) * coeff a x ^ 2 / θ :=
        Finset.sum_le_sum fun x _ => abs_shift_summand_le h0 h1 hθ coeff a x
    _ = (∑ x : κ, p * (1 - p) * coeff a x ^ 2) / θ := (Finset.sum_div _ _ _).symm
    _ ≤ sigmaSq / θ := by gcongr

/-! ### Decomposing trZ as shift plus linear process in trC -/

theorem trZ_eq_shift_add_lin (coeff : ι → κ → ℝ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (θ : ℝ) (ω : κ → Bool) :
    trZ coeff p θ ω =
      Finset.univ.sup' Finset.univ_nonempty
        (fun a : ι => trShift coeff p θ a +
          linSum (fun a x => trC coeff p θ a x) p a ω) := by
  have hfun : (fun a : ι => ∑ x : κ, trSmall coeff p θ a x (ω x)) =
      (fun a : ι => trShift coeff p θ a +
        linSum (fun a x => trC coeff p θ a x) p a ω) := by
    funext a
    calc ∑ x : κ, trSmall coeff p θ a x (ω x)
        = ∑ x : κ, ((bw p true * trSmall coeff p θ a x true +
              bw p false * trSmall coeff p θ a x false) +
            (cond (ω x) (1:ℝ) 0 - p) * trC coeff p θ a x) :=
          Finset.sum_congr rfl fun x _ => trSmall_affine h0 h1 coeff θ a x (ω x)
      _ = (∑ x : κ, (bw p true * trSmall coeff p θ a x true +
              bw p false * trSmall coeff p θ a x false)) +
            ∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * trC coeff p θ a x :=
          Finset.sum_add_distrib
      _ = trShift coeff p θ a + linSum (fun a x => trC coeff p θ a x) p a ω := rfl
  unfold trZ supProc
  rw [hfun]

/-! ### The sandwich -/

theorem trZ_sandwich {p θ sigmaSq : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ : 0 < θ)
    (coeff : ι → κ → ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq) (ω : κ → Bool) :
    |trZ coeff p θ ω - Zproc (fun a x => trC coeff p θ a x) p ω| ≤ sigmaSq / θ := by
  have hS : ∀ a : ι, |trShift coeff p θ a| ≤ sigmaSq / θ := fun a =>
    abs_trShift_le h0 h1 hθ coeff a (hVar a)
  have hle1 : Finset.univ.sup' Finset.univ_nonempty
      (fun a : ι => trShift coeff p θ a + linSum (fun a x => trC coeff p θ a x) p a ω) ≤
      Zproc (fun a x => trC coeff p θ a x) p ω + sigmaSq / θ := by
    apply Finset.sup'_le
    intro a _
    have h1' := (abs_le.mp (hS a)).2
    have h2' : linSum (fun a x => trC coeff p θ a x) p a ω ≤
        Zproc (fun a x => trC coeff p θ a x) p ω :=
      le_supProc (linSummand (fun a x => trC coeff p θ a x) p) ω a
    linarith
  have hle2 : Zproc (fun a x => trC coeff p θ a x) p ω ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun a : ι => trShift coeff p θ a +
          linSum (fun a x => trC coeff p θ a x) p a ω) + sigmaSq / θ := by
    unfold Zproc supProc
    apply Finset.sup'_le
    intro a _
    have h1' := (abs_le.mp (hS a)).1
    have h2' : trShift coeff p θ a + linSum (fun a x => trC coeff p θ a x) p a ω ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun a : ι => trShift coeff p θ a +
            linSum (fun a x => trC coeff p θ a x) p a ω) :=
      Finset.le_sup'
        (f := fun a : ι => trShift coeff p θ a +
          linSum (fun a x => trC coeff p θ a x) p a ω)
        (Finset.mem_univ a)
    have hdef : (∑ x : κ, linSummand (fun a x => trC coeff p θ a x) p a x (ω x)) =
        linSum (fun a x => trC coeff p θ a x) p a ω := rfl
    rw [hdef]
    linarith
  rw [trZ_eq_shift_add_lin coeff h0 h1 θ ω, abs_le]
  constructor
  · linarith
  · linarith

theorem abs_Ex_trZ_sub {p θ sigmaSq : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ : 0 < θ)
    (coeff : ι → κ → ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq) :
    |Ex p (trZ coeff p θ) - Ex p (Zproc (fun a x => trC coeff p θ a x) p)| ≤
      sigmaSq / θ := by
  have hup : ∀ ω : κ → Bool, trZ coeff p θ ω ≤
      Zproc (fun a x => trC coeff p θ a x) p ω + sigmaSq / θ := by
    intro ω
    have h := abs_le.mp (trZ_sandwich h0 h1 hθ coeff hVar ω)
    linarith [h.2]
  have hlo : ∀ ω : κ → Bool, Zproc (fun a x => trC coeff p θ a x) p ω ≤
      trZ coeff p θ ω + sigmaSq / θ := by
    intro ω
    have h := abs_le.mp (trZ_sandwich h0 h1 hθ coeff hVar ω)
    linarith [h.1]
  have hEx1 : Ex p (fun ω => Zproc (fun a x => trC coeff p θ a x) p ω + sigmaSq / θ) =
      Ex p (Zproc (fun a x => trC coeff p θ a x) p) + sigmaSq / θ := by
    have h := Ex_add (p := p) (Zproc (fun a x => trC coeff p θ a x) p)
      (fun _ => sigmaSq / θ)
    simpa [Ex_const h0 h1] using h
  have hEx2 : Ex p (fun ω => trZ coeff p θ ω + sigmaSq / θ) =
      Ex p (trZ coeff p θ) + sigmaSq / θ := by
    have h := Ex_add (p := p) (trZ coeff p θ) (fun _ => sigmaSq / θ)
    simpa [Ex_const h0 h1] using h
  have hm1 := Ex_mono h0 h1 hup
  have hm2 := Ex_mono h0 h1 hlo
  rw [hEx1] at hm1
  rw [hEx2] at hm2
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-! ### Zbar comparison and variance transfer -/

theorem trZbar_le {p θ sigmaSq : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hθ : 0 < θ)
    (coeff : ι → κ → ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq) (ω : κ → Bool) :
    Zbar (fun a x => trC coeff p θ a x) p ω ≤
      Zbar coeff p ω + Sigma2 coeff p ω / θ + sigmaSq / θ := by
  have htri : ∀ A B C : ℝ, |A - B - C| ≤ |A| + |B| + |C| := by
    intro A B C
    calc |A - B - C| = |A + -B + -C| := by
          rw [sub_eq_add_neg, sub_eq_add_neg]
      _ ≤ |A + -B| + |-C| := abs_add_le _ _
      _ ≤ |A| + |-B| + |-C| := by
          have h := abs_add_le A (-B)
          linarith
      _ = |A| + |B| + |C| := by rw [abs_neg, abs_neg]
  unfold Zbar
  apply Finset.sup'_le
  intro a _
  have hdecomp : ∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * trC coeff p θ a x =
      (∑ x : κ, trSmall coeff p θ a x (ω x)) - trShift coeff p θ a := by
    rw [eq_sub_iff_add_eq]
    unfold trShift
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h := trSmall_affine h0 h1 coeff θ a x (ω x)
    linarith
  have hsplit : (∑ x : κ, trSmall coeff p θ a x (ω x)) =
      (∑ x : κ, linSummand coeff p a x (ω x)) - ∑ x : κ, trBig coeff p θ a x (ω x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by unfold trBig; ring
  have h1b : |∑ x : κ, linSummand coeff p a x (ω x)| ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun a : ι => |∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x|) :=
    Finset.le_sup'
      (f := fun a : ι => |∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x|)
      (Finset.mem_univ a)
  have h2b : (∑ x : κ, |trBig coeff p θ a x (ω x)|) ≤ Sigma2 coeff p ω / θ :=
    le_trans (le_supProc (fun a x b => |trBig coeff p θ a x b|) ω a)
      (trW_le_Sigma2_div hθ coeff p ω)
  have h3b : |trShift coeff p θ a| ≤ sigmaSq / θ :=
    abs_trShift_le h0 h1 hθ coeff a (hVar a)
  have h4b : |∑ x : κ, trBig coeff p θ a x (ω x)| ≤
      ∑ x : κ, |trBig coeff p θ a x (ω x)| :=
    Finset.abs_sum_le_sum_abs _ _
  rw [hdecomp, hsplit]
  have h5b := htri (∑ x : κ, linSummand coeff p a x (ω x))
    (∑ x : κ, trBig coeff p θ a x (ω x)) (trShift coeff p θ a)
  linarith

theorem trC_sq_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ) (θ : ℝ)
    (a : ι) (x : κ) : trC coeff p θ a x ^ 2 ≤ coeff a x ^ 2 := by
  have habs := abs_trC_le_coeff h0 h1 coeff θ a x
  nlinarith [sq_abs (trC coeff p θ a x), sq_abs (coeff a x),
    abs_nonneg (trC coeff p θ a x)]

theorem trC_var_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ) (θ : ℝ)
    (a : ι) :
    ∑ x : κ, p * (1 - p) * trC coeff p θ a x ^ 2 ≤
      ∑ x : κ, p * (1 - p) * coeff a x ^ 2 := by
  refine Finset.sum_le_sum fun x _ => ?_
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg h0 (by linarith)
  exact mul_le_mul_of_nonneg_left (trC_sq_le h0 h1 coeff θ a x) hpp

theorem trC_Sigma2_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ) (θ : ℝ)
    (ω : κ → Bool) :
    Sigma2 (fun a x => trC coeff p θ a x) p ω ≤ Sigma2 coeff p ω := by
  unfold Sigma2
  apply Finset.sup'_le
  intro a _
  refine le_trans ?_
    (Finset.le_sup'
      (f := fun a : ι => ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - p) ^ 2)
      (Finset.mem_univ a))
  refine Finset.sum_le_sum fun x _ => ?_
  exact mul_le_mul_of_nonneg_right (trC_sq_le h0 h1 coeff θ a x) (sq_nonneg _)

end TalagrandCore
end

/-! ## Component: PoissonUpper -/
section
/-
Block T4 (part 1): coefficient-scaling identities, the Gaussian-regime Chernoff
tail from `gaussian_upper_cgf`, and its conversion to the log-form target on
the regime `log(1 + u/w₄) ≤ 200`.  (Part 2 — the truncation/Poissonian regime —
is appended below once `Truncation.lean` is available.)
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-! ### Scaling identities -/

theorem Zproc_smul (coeff : ι → κ → ℝ) (p : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (ω : κ → Bool) :
    Zproc (fun a x => c * coeff a x) p ω = c * Zproc coeff p ω := by
  unfold Zproc supProc
  have hbr : (fun a : ι =>
      ∑ x : κ, linSummand (fun a x => c * coeff a x) p a x (ω x)) =
      (fun a : ι => c * ∑ x : κ, linSummand coeff p a x (ω x)) := by
    funext a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show (cond (ω x) (1:ℝ) 0 - p) * (c * coeff a x) =
      c * ((cond (ω x) (1:ℝ) 0 - p) * coeff a x)
    ring
  rw [hbr, sup'_const_mul c hc]

theorem Zbar_smul (coeff : ι → κ → ℝ) (p : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (ω : κ → Bool) :
    Zbar (fun a x => c * coeff a x) p ω = c * Zbar coeff p ω := by
  unfold Zbar
  have hbr : (fun a : ι =>
      |∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * (c * coeff a x)|) =
      (fun a : ι =>
        c * |∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x|) := by
    funext a
    have hsum : ∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * (c * coeff a x) =
        c * ∑ x : κ, (cond (ω x) (1:ℝ) 0 - p) * coeff a x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hsum, abs_mul, abs_of_nonneg hc]
  rw [hbr, sup'_const_mul c hc]

theorem Sigma2_smul (coeff : ι → κ → ℝ) (p : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (ω : κ → Bool) :
    Sigma2 (fun a x => c * coeff a x) p ω = c ^ 2 * Sigma2 coeff p ω := by
  unfold Sigma2
  have hbr : (fun a : ι =>
      ∑ x : κ, (c * coeff a x) ^ 2 * (cond (ω x) (1:ℝ) 0 - p) ^ 2) =
      (fun a : ι =>
        c ^ 2 * ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1:ℝ) 0 - p) ^ 2) := by
    funext a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hbr, sup'_const_mul (c ^ 2) (sq_nonneg c)]

/-! ### Numeric exponential bounds and expectation helpers -/

private lemma exp_two_ge_seven : (7:ℝ) ≤ Real.exp 2 := by
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9]

private lemma exp_two_le : Real.exp 2 ≤ 7.39 := by
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

private lemma exp_four_le_hundred : Real.exp 4 ≤ 100 := by
  have h4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [exp_two_le, Real.exp_pos 2]

private lemma exp_two_hundred_ge : (30001:ℝ) ≤ Real.exp 200 := by
  have h50 : (51:ℝ) ≤ Real.exp 50 := by
    have := Real.add_one_le_exp (50:ℝ); linarith
  have h100e : Real.exp 100 = Real.exp 50 * Real.exp 50 := by
    rw [← Real.exp_add]; norm_num
  have h100 : (2601:ℝ) ≤ Real.exp 100 := by
    nlinarith [Real.exp_pos 50]
  have h200e : Real.exp 200 = Real.exp 100 * Real.exp 100 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos 100]

private lemma Ex_le_smul {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {F f : (κ → Bool) → ℝ} {c : ℝ} (hpt : ∀ ω, F ω ≤ c * f ω) :
    Ex p F ≤ c * Ex p f := by
  have h := Ex_mono h0 h1 hpt
  have hc := Ex_smul (p := p) c f
  linarith

private lemma Ex_le_affine {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {F f g : (κ → Bool) → ℝ} {c1 c2 c3 : ℝ}
    (hpt : ∀ ω, F ω ≤ c1 * f ω + (c2 * g ω + c3)) :
    Ex p F ≤ c1 * Ex p f + (c2 * Ex p g + c3) := by
  have h := Ex_mono h0 h1 hpt
  have hb := Ex_add (p := p) (fun ω => c1 * f ω) (fun ω => c2 * g ω + c3)
  have hb2 := Ex_add (p := p) (fun ω => c2 * g ω) (fun _ => c3)
  have hc := Ex_smul (p := p) c1 f
  have hd := Ex_smul (p := p) c2 g
  have he := Ex_const (κ := κ) (p := p) h0 h1 c3
  linarith

/-! ### Gaussian-regime Chernoff tail -/

/-- Chernoff from the Gaussian cgf bound: for `0 ≤ λ ≤ 1/8`,
`P(Z ≥ EZ + u) ≤ exp(−λu + 200λ²·w₄)`. -/
theorem gaussian_upper_tail (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ} (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    (u : ℝ) {lam : ℝ} (h0 : 0 ≤ lam) (h8 : lam ≤ 1/8) :
    Ex (p : ℝ) (fun ω => if Ex (p : ℝ) (Zproc coeff (p : ℝ)) + u ≤
        Zproc coeff (p : ℝ) ω then (1:ℝ) else 0) ≤
      Real.exp (-(lam * u) + 200 * lam ^ 2 *
        (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
          Ex (p : ℝ) (Zbar coeff (p : ℝ)))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set EZ := Ex (p : ℝ) (Zproc coeff (p : ℝ)) with hEZ
  have hch := chernoff_upper h0p h1p (Zproc coeff (p : ℝ))
    (lam := lam) (s := EZ + u) h0
  have hcgf := gaussian_upper_cgf p hp coeff hB sigmaSq hs hVar lam h0 h8
  -- Ex e^{λZ} = e^{λ·EZ} · Ex e^{λ(Z−EZ)}
  have hsplit : Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω)) =
      Real.exp (lam * EZ) *
        Ex (p : ℝ) (fun ω => Real.exp (lam *
          (Zproc coeff (p : ℝ) ω - EZ))) := by
    rw [← Ex_smul]
    refine Ex_congr fun ω => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  have hmgf_pos : 0 < Ex (p : ℝ)
      (fun ω => Real.exp (lam * (Zproc coeff (p : ℝ) ω - EZ))) :=
    Ex_pos h0p h1p fun ω => Real.exp_pos _
  have hmgf : Ex (p : ℝ)
      (fun ω => Real.exp (lam * (Zproc coeff (p : ℝ) ω - EZ))) ≤
      Real.exp (200 * lam ^ 2 *
        (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
          Ex (p : ℝ) (Zbar coeff (p : ℝ)))) := by
    rw [← Real.exp_log hmgf_pos]
    exact Real.exp_le_exp.mpr hcgf
  calc Ex (p : ℝ) (fun ω => if EZ + u ≤ Zproc coeff (p : ℝ) ω
        then (1:ℝ) else 0) ≤
      Real.exp (-(lam * (EZ + u))) *
        Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω)) := hch
    _ = Real.exp (-(lam * (EZ + u))) * Real.exp (lam * EZ) *
        Ex (p : ℝ) (fun ω => Real.exp (lam *
          (Zproc coeff (p : ℝ) ω - EZ))) := by
        rw [hsplit]; ring
    _ ≤ Real.exp (-(lam * (EZ + u))) * Real.exp (lam * EZ) *
        Real.exp (200 * lam ^ 2 *
          (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
            Ex (p : ℝ) (Zbar coeff (p : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left hmgf
        positivity
    _ = Real.exp (-(lam * u) + 200 * lam ^ 2 *
        (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
          Ex (p : ℝ) (Zbar coeff (p : ℝ)))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-- Gaussian-regime conversion to the log-form target: valid whenever
`log(1 + u/w₄) ≤ 200`. -/
theorem poisson_upper_regimeA (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ} (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {u : ℝ} (hu : 0 ≤ u)
    (hw : 0 < sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
      Ex (p : ℝ) (Zbar coeff (p : ℝ)))
    (hL : Real.log (1 + u / (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
      Ex (p : ℝ) (Zbar coeff (p : ℝ)))) ≤ 200) :
    Ex (p : ℝ) (fun ω => if Ex (p : ℝ) (Zproc coeff (p : ℝ)) + u ≤
        Zproc coeff (p : ℝ) ω then (1:ℝ) else 0) ≤
      Real.exp (-((u / 3200) *
        Real.log (1 + u / (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
          Ex (p : ℝ) (Zbar coeff (p : ℝ)))))) := by
  set w4 := sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
    Ex (p : ℝ) (Zbar coeff (p : ℝ)) with hw4
  have hLnn : 0 ≤ Real.log (1 + u / w4) :=
    Real.log_nonneg (by
      have : 0 ≤ u / w4 := div_nonneg hu hw.le
      linarith)
  rcases le_total u (50 * w4) with hcase | hcase
  · -- λ := u/(400·w₄) ≤ 1/8
    have hlam0 : 0 ≤ u / (400 * w4) := by positivity
    have hlam8 : u / (400 * w4) ≤ 1/8 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h := gaussian_upper_tail p hp coeff hB hs hVar u hlam0 hlam8
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    have hexp : -(u / (400 * w4) * u) + 200 * (u / (400 * w4)) ^ 2 * w4 =
        -(u ^ 2 / (800 * w4)) := by
      field_simp
      ring
    rw [← hw4] at *
    rw [hexp]
    -- −u²/(800w₄) ≤ −(u/3200)·log(1+u/w₄) since log(1+x) ≤ x
    have hlogle : Real.log (1 + u / w4) ≤ u / w4 := by
      have h1 : (0:ℝ) < 1 + u / w4 := by
        have : 0 ≤ u / w4 := div_nonneg hu hw.le
        linarith
      have := Real.log_le_sub_one_of_pos h1
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlogle (by positivity : (0:ℝ) ≤ u / 3200)
    have hident : u / 3200 * (u / w4) ≤ u ^ 2 / (800 * w4) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      ring_nf
      nlinarith [sq_nonneg u, hw, mul_nonneg (mul_nonneg hu hu) hw.le]
    linarith
  · -- λ := 1/8 branch: exponent ≤ −u/16, and (u/3200)·log ≤ (u/3200)·200 = u/16
    have h := gaussian_upper_tail p hp coeff hB hs hVar u
      (le_refl (0:ℝ) |>.trans (by norm_num : (0:ℝ) ≤ 1/8)) (le_refl (1/8 : ℝ))
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    rw [← hw4] at *
    have h1 : -(1/8 * u) + 200 * (1/8:ℝ) ^ 2 * w4 ≤ -(u/16) := by
      have : 200 * (1/8:ℝ) ^ 2 * w4 ≤ (25/8) * (u / 50) := by
        nlinarith [hcase]
      nlinarith
    have h2 : (u / 3200) * Real.log (1 + u / w4) ≤ u / 16 := by
      have := mul_le_mul_of_nonneg_left hL
        (by positivity : (0:ℝ) ≤ u / 3200)
      nlinarith
    linarith

set_option maxHeartbeats 3200000 in
/-- **T4 (Poissonian upper tail).** For the linear class with `|coeff| ≤ 1`,
`P(Z ≥ EZ + u) ≤ 3·exp(−(u/3200)·log(1 + u/w₄))`, `w₄ = σ² + EΣ² + EZ̄`. -/
theorem poisson_upper_tail (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ} (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {u : ℝ} (hu : 0 ≤ u)
    (hw4 : 0 < sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
      Ex (p : ℝ) (Zbar coeff (p : ℝ))) :
    Ex (p : ℝ) (fun ω => if Ex (p : ℝ) (Zproc coeff (p : ℝ)) + u ≤
        Zproc coeff (p : ℝ) ω then (1:ℝ) else 0) ≤
      3 * Real.exp (-((u / 3200) *
        Real.log (1 + u / (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
          Ex (p : ℝ) (Zbar coeff (p : ℝ)))))) := by
  have p0 : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have p1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hES0 : 0 ≤ Ex (p:ℝ) (Sigma2 coeff (p:ℝ)) :=
    Ex_nonneg p0 p1 fun ω => Sigma2_nonneg coeff (p:ℝ) ω
  have hEZb0 : 0 ≤ Ex (p:ℝ) (Zbar coeff (p:ℝ)) :=
    Ex_nonneg p0 p1 fun ω => Zbar_nonneg coeff (p:ℝ) ω
  set w4 := sigmaSq + Ex (p:ℝ) (Sigma2 coeff (p:ℝ)) + Ex (p:ℝ) (Zbar coeff (p:ℝ))
    with hw4def
  have hσw : sigmaSq ≤ w4 := by rw [hw4def]; linarith
  have hESw : Ex (p:ℝ) (Sigma2 coeff (p:ℝ)) ≤ w4 := by rw [hw4def]; linarith
  have hEZbw : Ex (p:ℝ) (Zbar coeff (p:ℝ)) ≤ w4 := by rw [hw4def]; linarith
  rcases le_total (Real.log (1 + u / w4)) 200 with hL | hL
  · -- Regime A: `log(1 + u/w₄) ≤ 200`
    have h := poisson_upper_regimeA p hp coeff hB hs hVar hu hw4 hL
    rw [← hw4def] at h
    have he := Real.exp_pos (-(u / 3200 * Real.log (1 + u / w4)))
    linarith
  · -- Regime B: `log(1 + u/w₄) ≥ 200`
    have h1uw : (0:ℝ) < 1 + u / w4 := by
      have h : 0 ≤ u / w4 := div_nonneg hu hw4.le
      linarith
    have hExp200 : Real.exp 200 ≤ 1 + u / w4 := by
      rw [← Real.exp_log h1uw]
      exact Real.exp_le_exp.mpr hL
    have huw : (30000:ℝ) ≤ u / w4 := by
      have h := exp_two_hundred_ge
      linarith
    have hupos : (0:ℝ) < u := by
      rcases hu.lt_or_eq with h | h
      · exact h
      · rw [← h, zero_div] at huw; norm_num at huw
    set t' := u / 3 with ht'def
    have ht'pos : (0:ℝ) < t' := by
      rw [ht'def]; exact div_pos hupos (by norm_num)
    have ht'ne : t' ≠ 0 := ht'pos.ne'
    have hu3 : u = 3 * t' := by rw [ht'def]; ring
    have hxw : (10000:ℝ) ≤ t' / w4 := by
      have h : t' / w4 = u / w4 / 3 := by rw [ht'def, div_right_comm]
      rw [h]; linarith
    set s0 := Real.sqrt (w4 * t') with hs0def
    have hwt : (0:ℝ) < w4 * t' := mul_pos hw4 ht'pos
    have hs0pos : (0:ℝ) < s0 := by rw [hs0def]; exact Real.sqrt_pos.mpr hwt
    have hs0ne : s0 ≠ 0 := hs0pos.ne'
    have hs0sq : s0 ^ 2 = w4 * t' := by rw [hs0def]; exact Real.sq_sqrt hwt.le
    set θ := s0 / t' with hθdef
    have hθpos : (0:ℝ) < θ := by rw [hθdef]; exact div_pos hs0pos ht'pos
    have hθne : θ ≠ 0 := hθpos.ne'
    set R := t' / s0 with hRdef
    have hRpos : (0:ℝ) < R := by rw [hRdef]; exact div_pos ht'pos hs0pos
    -- algebraic identities
    have hs0t : s0 = θ * t' := by rw [hθdef, div_mul_cancel₀ _ ht'ne]
    have hRs0 : R * s0 = t' := by rw [hRdef, div_mul_cancel₀ _ hs0ne]
    have hθR : θ * R = 1 := by
      rw [hθdef, hRdef, div_mul_div_comm, mul_comm t' s0]
      exact div_self (mul_ne_zero hs0ne ht'ne)
    have hw4tt : w4 = θ ^ 2 * t' := by
      refine mul_right_cancel₀ ht'ne ?_
      have h : (θ * t') ^ 2 = w4 * t' := by rw [← hs0t]; exact hs0sq
      linarith [h]
    have hw4s : w4 = θ * s0 := by rw [hw4tt, hs0t]; ring
    have hw4θ : w4 / θ = s0 := by
      rw [hw4s, mul_comm θ s0, mul_div_assoc, div_self hθne, mul_one]
    have ht'R2 : t' = R ^ 2 * w4 := by
      refine mul_right_cancel₀ ht'ne ?_
      have h1 : (R * s0) ^ 2 = t' ^ 2 := by rw [hRs0]
      linear_combination R ^ 2 * hs0sq - h1
    have hθt'R : θ * (t' * R) = t' := by linear_combination t' * hθR
    have hR100 : (100:ℝ) ≤ R := by
      have h1 : (10000:ℝ) * w4 ≤ t' := (le_div_iff₀ hw4).mp hxw
      have h2 : (10000:ℝ) ≤ R ^ 2 := by
        have h3 : (10000:ℝ) * w4 ≤ R ^ 2 * w4 := by rw [← ht'R2]; exact h1
        exact le_of_mul_le_mul_right h3 hw4
      nlinarith [hRpos, h2]
    have h100s0 : 100 * s0 ≤ t' := by nlinarith [hRs0, hR100, hs0pos]
    have hs0t' : s0 ≤ t' := by linarith
    -- division bounds
    have hESt : Ex (p:ℝ) (Sigma2 coeff (p:ℝ)) / θ ≤ s0 := by
      rw [← hw4θ]
      exact (div_le_div_iff_of_pos_right hθpos).mpr hESw
    have hσθ : sigmaSq / θ ≤ s0 := by
      rw [← hw4θ]
      exact (div_le_div_iff_of_pos_right hθpos).mpr hσw
    -- log bounds
    have hlogR4 : (4:ℝ) ≤ Real.log R :=
      (Real.le_log_iff_exp_le hRpos).mpr (le_trans exp_four_le_hundred hR100)
    have hlogRR : Real.log R ≤ R - 1 := Real.log_le_sub_one_of_pos hRpos
    have hLle : Real.log (1 + u / w4) ≤ 2 + 2 * Real.log R := by
      rw [Real.log_le_iff_le_exp h1uw]
      have hexpand : Real.exp (2 + 2 * Real.log R) = Real.exp 2 * (R * R) := by
        rw [show (2:ℝ) + 2 * Real.log R = 2 + (Real.log R + Real.log R) by ring,
          Real.exp_add, Real.exp_add, Real.exp_log hRpos]
      have huwR : u / w4 = 3 * R ^ 2 := by
        rw [hu3, ht'R2, mul_div_assoc, mul_div_assoc, div_self hw4.ne', mul_one]
      have hRR : (10000:ℝ) ≤ R * R := by nlinarith [hR100]
      rw [hexpand, huwR]
      nlinarith [hRR, exp_two_ge_seven]
    -- the W (big-part) tail
    have hWtail : Ex (p:ℝ) (fun ω => if t' ≤ trW coeff (p:ℝ) θ ω then (1:ℝ) else 0) ≤
        Real.exp (-(t' * Real.log (t' / s0) - t' + s0)) := by
      have hm : Ex (p:ℝ)
          (fun ω => supProc (fun a x b => |trBig coeff (p:ℝ) θ a x b|) ω) ≤ s0 :=
        le_trans (Ex_trW_le p0 p1 hθpos coeff) hESt
      exact poisson_tail p hp (fun a x b => |trBig coeff (p:ℝ) θ a x b|)
        (fun a x b => abs_nonneg _) (fun a x b => abs_trBig_le_one p0 p1 hB θ a x b)
        hm hs0pos hs0t'
    have hWexp : u / 3200 * Real.log (1 + u / w4) ≤
        t' * Real.log (t' / s0) - t' + s0 := by
      rw [← hRdef]
      have hstep : u / 3200 * Real.log (1 + u / w4) ≤
          u / 3200 * (2 + 2 * Real.log R) :=
        mul_le_mul_of_nonneg_left hLle (div_nonneg hu (by norm_num))
      have hueq : u / 3200 * (2 + 2 * Real.log R) =
          3 * t' / 3200 * (2 + 2 * Real.log R) := by rw [hu3]
      have hP2 : 0 ≤ t' * (Real.log R - 4) := mul_nonneg ht'pos.le (by linarith)
      linarith [hstep, hueq, hP2, hs0pos, ht'pos]
    have hW : Ex (p:ℝ) (fun ω => if t' ≤ trW coeff (p:ℝ) θ ω then (1:ℝ) else 0) ≤
        Real.exp (-(u / 3200 * Real.log (1 + u / w4))) :=
      le_trans hWtail (Real.exp_le_exp.mpr (by linarith [hWexp]))
    -- event split: {Z ≥ EZ + u} ⊆ {trZ ≥ EZ + 2t'} ∪ {trW ≥ t'}
    have hpt : ∀ ω, (if Ex (p:ℝ) (Zproc coeff (p:ℝ)) + u ≤ Zproc coeff (p:ℝ) ω
          then (1:ℝ) else 0) ≤
        (if Ex (p:ℝ) (Zproc coeff (p:ℝ)) + 2 * t' ≤ trZ coeff (p:ℝ) θ ω
          then (1:ℝ) else 0) +
        (if t' ≤ trW coeff (p:ℝ) θ ω then (1:ℝ) else 0) := by
      intro ω
      by_cases h1 : Ex (p:ℝ) (Zproc coeff (p:ℝ)) + 2 * t' ≤ trZ coeff (p:ℝ) θ ω
      · rw [if_pos h1]
        have h2 : (0:ℝ) ≤ if t' ≤ trW coeff (p:ℝ) θ ω then (1:ℝ) else 0 := by
          split <;> norm_num
        have h3 : (if Ex (p:ℝ) (Zproc coeff (p:ℝ)) + u ≤ Zproc coeff (p:ℝ) ω
            then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
        linarith
      · by_cases h2 : t' ≤ trW coeff (p:ℝ) θ ω
        · rw [if_neg h1, if_pos h2]
          have h3 : (if Ex (p:ℝ) (Zproc coeff (p:ℝ)) + u ≤ Zproc coeff (p:ℝ) ω
              then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
          linarith
        · have hno : ¬ (Ex (p:ℝ) (Zproc coeff (p:ℝ)) + u ≤ Zproc coeff (p:ℝ) ω) := by
            push_neg at h1 h2 ⊢
            have h3 := Zproc_le_trZ_add_trW coeff (p:ℝ) θ ω
            rw [hu3]
            linarith
          rw [if_neg h1, if_neg h2, if_neg hno]
          norm_num
    have hsplit : Ex (p:ℝ) (fun ω => if Ex (p:ℝ) (Zproc coeff (p:ℝ)) + u ≤
          Zproc coeff (p:ℝ) ω then (1:ℝ) else 0) ≤
        Ex (p:ℝ) (fun ω => if Ex (p:ℝ) (Zproc coeff (p:ℝ)) + 2 * t' ≤
          trZ coeff (p:ℝ) θ ω then (1:ℝ) else 0) +
        Ex (p:ℝ) (fun ω => if t' ≤ trW coeff (p:ℝ) θ ω then (1:ℝ) else 0) :=
      le_trans (Ex_mono p0 p1 hpt) (le_of_eq (Ex_add _ _))
    -- rescaled truncated coefficients
    set C2 : ι → κ → ℝ := fun a x => trC coeff (p:ℝ) θ a x / (2 * θ) with hC2def
    have h2θpos : (0:ℝ) < 2 * θ := by linarith
    have h2θne : (2:ℝ) * θ ≠ 0 := h2θpos.ne'
    have hC2scale : (fun a x => trC coeff (p:ℝ) θ a x) =
        (fun a x => 2 * θ * C2 a x) := by
      funext a x
      simp only [hC2def]
      rw [mul_comm (2 * θ) (trC coeff (p:ℝ) θ a x / (2 * θ)),
        div_mul_cancel₀ _ h2θne]
    have hZC2 : ∀ ω, Zproc (fun a x => trC coeff (p:ℝ) θ a x) (p:ℝ) ω =
        2 * θ * Zproc C2 (p:ℝ) ω := by
      intro ω
      rw [hC2scale]
      exact Zproc_smul C2 (p:ℝ) h2θpos.le ω
    have hEZC2 : Ex (p:ℝ) (Zproc (fun a x => trC coeff (p:ℝ) θ a x) (p:ℝ)) =
        2 * θ * Ex (p:ℝ) (Zproc C2 (p:ℝ)) := by
      rw [← Ex_smul]
      exact Ex_congr hZC2
    -- mean comparisons
    have hExtrW : Ex (p:ℝ) (trW coeff (p:ℝ) θ) ≤ s0 :=
      le_trans (Ex_trW_le p0 p1 hθpos coeff) hESt
    have hEtrZ : Ex (p:ℝ) (trZ coeff (p:ℝ) θ) ≤ Ex (p:ℝ) (Zproc coeff (p:ℝ)) + s0 := by
      have h1 := Ex_mono p0 p1 (trZ_le_Zproc_add_trW coeff (p:ℝ) θ)
      rw [Ex_add (Zproc coeff (p:ℝ)) (trW coeff (p:ℝ) θ)] at h1
      linarith
    have hEZ'le : Ex (p:ℝ) (Zproc (fun a x => trC coeff (p:ℝ) θ a x) (p:ℝ)) ≤
        Ex (p:ℝ) (trZ coeff (p:ℝ) θ) + s0 := by
      have h1 := (abs_le.mp (abs_Ex_trZ_sub p0 p1 hθpos coeff hVar)).1
      linarith [hσθ]
    have hEZ2u : 2 * θ * Ex (p:ℝ) (Zproc C2 (p:ℝ)) ≤
        Ex (p:ℝ) (Zproc coeff (p:ℝ)) + 2 * s0 := by
      rw [← hEZC2]
      linarith [hEZ'le, hEtrZ]
    -- pointwise event transfer to the rescaled process
    have hZimp : ∀ ω, Ex (p:ℝ) (Zproc coeff (p:ℝ)) + 2 * t' ≤ trZ coeff (p:ℝ) θ ω →
        Ex (p:ℝ) (Zproc C2 (p:ℝ)) + 3 / 4 * (t' * R) ≤ Zproc C2 (p:ℝ) ω := by
      intro ω hA
      have hsand := (abs_le.mp (trZ_sandwich p0 p1 hθpos coeff hVar ω)).2
      have hZω := hZC2 ω
      refine le_of_mul_le_mul_left ?_ h2θpos
      linarith [hA, hsand, hσθ, hZω, hEZ2u, h100s0, hθt'R, ht'pos, hs0pos]
    -- Gaussian data for the rescaled truncated process
    have hB2 : ∀ a x, |C2 a x| ≤ 1 := by
      intro a x
      simp only [hC2def]
      rw [abs_div, abs_of_pos h2θpos, div_le_one h2θpos]
      exact abs_trC_le_two_theta hθpos.le coeff (p:ℝ) a x
    have ht'4 : (0:ℝ) ≤ t' / 4 := by linarith
    have hθθpos : (0:ℝ) < θ * θ := mul_pos hθpos hθpos
    have hVar2 : ∀ a, ∑ x : κ, (p:ℝ) * (1 - (p:ℝ)) * C2 a x ^ 2 ≤ t' / 4 := by
      intro a
      have h1 : ∀ x : κ, 4 * θ * θ * ((p:ℝ) * (1 - (p:ℝ)) * C2 a x ^ 2) =
          (p:ℝ) * (1 - (p:ℝ)) * (2 * θ * C2 a x) ^ 2 := by
        intro x; ring
      have h2 : ∀ x : κ, (2 * θ * C2 a x) ^ 2 = trC coeff (p:ℝ) θ a x ^ 2 := by
        intro x
        rw [← congrFun (congrFun hC2scale a) x]
      have h3 : (4 * θ * θ) * ∑ x : κ, (p:ℝ) * (1 - (p:ℝ)) * C2 a x ^ 2 =
          ∑ x : κ, (p:ℝ) * (1 - (p:ℝ)) * trC coeff (p:ℝ) θ a x ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by rw [h1 x, h2 x]
      have h4 : ∑ x : κ, (p:ℝ) * (1 - (p:ℝ)) * trC coeff (p:ℝ) θ a x ^ 2 ≤ sigmaSq :=
        le_trans (trC_var_le p0 p1 coeff θ a) (hVar a)
      have h5 : (θ * θ) * (4 * ∑ x : κ, (p:ℝ) * (1 - (p:ℝ)) * C2 a x ^ 2) ≤
          (θ * θ) * t' := by
        linarith [h3, h4, hσw, hw4tt]
      have h6 := le_of_mul_le_mul_left h5 hθθpos
      linarith [h6]
    -- mean of the rescaled variance process
    have hES2 : Ex (p:ℝ) (Sigma2 C2 (p:ℝ)) ≤ t' / 4 := by
      have hpt2 : ∀ ω, 4 * θ * θ * Sigma2 C2 (p:ℝ) ω ≤ Sigma2 coeff (p:ℝ) ω := by
        intro ω
        have h1 : Sigma2 (fun a x => trC coeff (p:ℝ) θ a x) (p:ℝ) ω =
            (2 * θ) ^ 2 * Sigma2 C2 (p:ℝ) ω := by
          rw [hC2scale]
          exact Sigma2_smul C2 (p:ℝ) h2θpos.le ω
        have h2 := trC_Sigma2_le p0 p1 coeff θ ω
        rw [h1] at h2
        linarith [h2]
      have h3 : Ex (p:ℝ) (fun ω => 4 * θ * θ * Sigma2 C2 (p:ℝ) ω) ≤
          Ex (p:ℝ) (Sigma2 coeff (p:ℝ)) := Ex_mono p0 p1 hpt2
      rw [Ex_smul (p := (p:ℝ)) (4 * θ * θ) (Sigma2 C2 (p:ℝ))] at h3
      have h5 : (θ * θ) * (4 * Ex (p:ℝ) (Sigma2 C2 (p:ℝ))) ≤ (θ * θ) * t' := by
        linarith [h3, hESw, hw4tt]
      have h6 := le_of_mul_le_mul_left h5 hθθpos
      linarith [h6]
    -- mean of the rescaled Zbar process
    have hEZb2 : Ex (p:ℝ) (Zbar C2 (p:ℝ)) ≤ 201 / 200 * t' := by
      have hpt3 : ∀ ω, 2 * θ * θ * Zbar C2 (p:ℝ) ω ≤
          θ * Zbar coeff (p:ℝ) ω + (1 * Sigma2 coeff (p:ℝ) ω + sigmaSq) := by
        intro ω
        have h1 : Zbar (fun a x => trC coeff (p:ℝ) θ a x) (p:ℝ) ω =
            2 * θ * Zbar C2 (p:ℝ) ω := by
          rw [hC2scale]
          exact Zbar_smul C2 (p:ℝ) h2θpos.le ω
        have h2 := trZbar_le p0 p1 hθpos coeff hVar ω
        rw [h1] at h2
        have h3 := mul_le_mul_of_nonneg_left h2 hθpos.le
        have hc1 : Sigma2 coeff (p:ℝ) ω / θ * θ = Sigma2 coeff (p:ℝ) ω :=
          div_mul_cancel₀ _ hθne
        have hc2 : sigmaSq / θ * θ = sigmaSq := div_mul_cancel₀ _ hθne
        linarith [h3, hc1, hc2]
      have hmean := Ex_le_affine p0 p1 hpt3
      rw [Ex_smul (p := (p:ℝ)) (2 * θ * θ) (Zbar C2 (p:ℝ))] at hmean
      have hb1 : θ * Ex (p:ℝ) (Zbar coeff (p:ℝ)) ≤ θ * (θ * s0) := by
        have h := mul_le_mul_of_nonneg_left hEZbw hθpos.le
        rw [hw4s] at h
        exact h
      have h5 : (θ * θ) * (2 * Ex (p:ℝ) (Zbar C2 (p:ℝ))) ≤ (θ * θ) * (s0 + 2 * t') := by
        linarith [hmean, hb1, hESw, hσw, hw4tt]
      have h6 := le_of_mul_le_mul_left h5 hθθpos
      linarith [h6, h100s0, ht'pos]
    -- Gaussian tail at deviation (3/4)·t'·R with λ = 1/8
    have hgauss := gaussian_upper_tail p hp C2 hB2 ht'4 hVar2 (3 / 4 * (t' * R))
      (by norm_num : (0:ℝ) ≤ 1/8) (le_refl (1/8 : ℝ))
    have hZev : Ex (p:ℝ) (fun ω => if Ex (p:ℝ) (Zproc coeff (p:ℝ)) + 2 * t' ≤
          trZ coeff (p:ℝ) θ ω then (1:ℝ) else 0) ≤
        Ex (p:ℝ) (fun ω => if Ex (p:ℝ) (Zproc C2 (p:ℝ)) + 3 / 4 * (t' * R) ≤
          Zproc C2 (p:ℝ) ω then (1:ℝ) else 0) := by
      refine Ex_mono p0 p1 fun ω => ?_
      by_cases h1 : Ex (p:ℝ) (Zproc coeff (p:ℝ)) + 2 * t' ≤ trZ coeff (p:ℝ) θ ω
      · rw [if_pos h1, if_pos (hZimp ω h1)]
      · rw [if_neg h1]
        split <;> norm_num
    have hZexp : -(1 / 8 * (3 / 4 * (t' * R))) + 200 * (1 / 8) ^ 2 *
          (t' / 4 + Ex (p:ℝ) (Sigma2 C2 (p:ℝ)) + Ex (p:ℝ) (Zbar C2 (p:ℝ))) ≤
        -(u / 3200 * Real.log (1 + u / w4)) := by
      have hstep : u / 3200 * Real.log (1 + u / w4) ≤
          u / 3200 * (2 + 2 * Real.log R) :=
        mul_le_mul_of_nonneg_left hLle (div_nonneg hu (by norm_num))
      have hueq : u / 3200 * (2 + 2 * Real.log R) =
          3 * t' / 3200 * (2 + 2 * Real.log R) := by rw [hu3]
      have hP3 : 0 ≤ t' * (R - 1 - Real.log R) :=
        mul_nonneg ht'pos.le (by linarith [hlogRR])
      have hP4 : 0 ≤ t' * (R - 100) := mul_nonneg ht'pos.le (by linarith)
      linarith [hstep, hueq, hP3, hP4, hES2, hEZb2, ht'pos]
    have hZ : Ex (p:ℝ) (fun ω => if Ex (p:ℝ) (Zproc coeff (p:ℝ)) + 2 * t' ≤
          trZ coeff (p:ℝ) θ ω then (1:ℝ) else 0) ≤
        Real.exp (-(u / 3200 * Real.log (1 + u / w4))) :=
      le_trans hZev (le_trans hgauss (Real.exp_le_exp.mpr hZexp))
    have he := Real.exp_pos (-(u / 3200 * Real.log (1 + u / w4)))
    linarith [hsplit, hZ, hW, he]

end TalagrandCore
end

/-! ## Component: KRCore -/
section
/-
Klein–Rio core, part 1: the generalized tensorization (their Proposition 2.1)
in sum-land, from `entropy_tensor_log` + a per-fiber Gibbs/duality inequality
(both ultimately `log w ≤ w − 1`).

  Ent(f) ≤ ∑_x ( Ex[g x·log(g x/condEx x (g x))] + Ex[(f − g x)·log(f/condEx x f)] )

for positive f and arbitrary positive g x.
-/

open scoped BigOperators

namespace TalagrandCore

variable {κ : Type} [DecidableEq κ] [Fintype κ]

/-- `condEx` of a product with an `x`-fiber-constant factor pulls the factor out. -/
theorem condEx_mul_fiberconst (p : ℝ) (x : κ) (f C : (κ → Bool) → ℝ)
    (hC : FiberConst x C) (ω : κ → Bool) :
    condEx p x (fun ω' => f ω' * C ω') ω = condEx p x f ω * C ω := by
  show bw p true * (f (Function.update ω x true) * C (Function.update ω x true)) +
      bw p false * (f (Function.update ω x false) * C (Function.update ω x false)) =
    (bw p true * f (Function.update ω x true) +
      bw p false * f (Function.update ω x false)) * C ω
  rw [hC ω true, hC ω false]
  ring

/-- Positivity of `condEx` for positive integrands. -/
theorem condEx_pos {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : κ) {f : (κ → Bool) → ℝ}
    (hf : ∀ ω, 0 < f ω) (ω : κ → Bool) : 0 < condEx p x f ω := by
  unfold condEx
  have hbt := bw_nonneg (p := p) h0 h1 true
  have hbf := bw_nonneg (p := p) h0 h1 false
  have hsum := bw_sum p
  have h1' := hf (Function.update ω x true)
  have h2' := hf (Function.update ω x false)
  rcases eq_or_lt_of_le hbt with h | h
  · have : bw p false = 1 := by linarith
    nlinarith
  · nlinarith

/-- `condEx` is `x`-fiber constant. -/
theorem fiberConst_condEx (p : ℝ) (x : κ) (f : (κ → Bool) → ℝ) :
    FiberConst x (condEx p x f) :=
  fun ω t => condEx_apply_update x f ω t

/-- Expectation against a fiber-constant weight: `Ex[f·C] = Ex[(condEx f)·C]`. -/
theorem Ex_mul_fiberconst {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : κ)
    (f C : (κ → Bool) → ℝ) (hC : FiberConst x C) :
    Ex p (fun ω => f ω * C ω) = Ex p (fun ω => condEx p x f ω * C ω) := by
  rw [← Ex_condEx h0 h1 x (fun ω => f ω * C ω)]
  exact Ex_congr fun ω => condEx_mul_fiberconst p x f C hC ω

/-- Per-fiber Gibbs inequality (pointwise form): if `condEx e^h = 1` on the
fiber of `ω`, then `condEx (g·h) ≤ condEx (g·log(g / condEx g))`. -/
theorem fiber_gibbs {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : κ)
    (g h : (κ → Bool) → ℝ) (hg : ∀ ω, 0 < g ω)
    (ω : κ → Bool)
    (hh : condEx p x (fun ω' => Real.exp (h ω')) ω = 1) :
    condEx p x (fun ω' => g ω' * h ω') ω ≤
      condEx p x (fun ω' => g ω' * Real.log (g ω' / condEx p x g ω')) ω := by
  -- Pointwise Young: g·h ≤ g·log(g/E_x g) + (E_x g)·e^h − g   (log w ≤ w − 1).
  have hEg : ∀ t, condEx p x g (Function.update ω x t) = condEx p x g ω :=
    fun t => condEx_apply_update x g ω t
  have hEgpos : 0 < condEx p x g ω := condEx_pos h0 h1 x hg ω
  have hyoung : ∀ ω', condEx p x g ω' = condEx p x g ω →
      g ω' * h ω' ≤ g ω' * Real.log (g ω' / condEx p x g ω') +
        condEx p x g ω * Real.exp (h ω') - g ω' := by
    intro ω' hωeq
    have hgpos := hg ω'
    have hw : (0:ℝ) < Real.exp (h ω') * condEx p x g ω / g ω' := by positivity
    have hlog := Real.log_le_sub_one_of_pos hw
    have hexpand : Real.log (Real.exp (h ω') * condEx p x g ω / g ω') =
        h ω' + Real.log (condEx p x g ω) - Real.log (g ω') := by
      rw [Real.log_div (by positivity) (ne_of_gt hgpos),
        Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hEgpos), Real.log_exp]
    rw [hexpand] at hlog
    have hlogdiv : Real.log (g ω' / condEx p x g ω') =
        Real.log (g ω') - Real.log (condEx p x g ω) := by
      rw [hωeq, Real.log_div (ne_of_gt hgpos) (ne_of_gt hEgpos)]
    rw [hlogdiv]
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hgpos)
    have hfield : g ω' * (Real.exp (h ω') * condEx p x g ω / g ω' - 1) =
        condEx p x g ω * Real.exp (h ω') - g ω' := by
      field_simp
    nlinarith [hmul, hfield]
  -- Average the Young inequality over the two fiber points.
  have hbt := bw_nonneg (p := p) h0 h1 true
  have hbf := bw_nonneg (p := p) h0 h1 false
  set uT := Function.update ω x true with huT
  set uF := Function.update ω x false with huF
  have hyT := hyoung uT (hEg true)
  have hyF := hyoung uF (hEg false)
  rw [hEg true] at hyT
  rw [hEg false] at hyF
  have hhh : bw p true * Real.exp (h uT) + bw p false * Real.exp (h uF) = 1 := hh
  have hEgdef : condEx p x g ω = bw p true * g uT + bw p false * g uF := rfl
  show bw p true * (g uT * h uT) + bw p false * (g uF * h uF) ≤
    bw p true * (g uT * Real.log (g uT / condEx p x g uT)) +
      bw p false * (g uF * Real.log (g uF / condEx p x g uF))
  rw [hEg true, hEg false]
  nlinarith [mul_le_mul_of_nonneg_left hyT hbt, mul_le_mul_of_nonneg_left hyF hbf,
    hhh, hEgdef]

/-- Per-coordinate entropy identity:
`Ex[f log f] − Ex[(E_x f)·log(E_x f)] = Ex[f·log(f/E_x f)]`. -/
theorem entropy_percoord_identity {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (f : (κ → Bool) → ℝ) (hf : ∀ ω, 0 < f ω) (x : κ) :
    Ex p (fun ω => f ω * Real.log (f ω)) -
      Ex p (fun ω => condEx p x f ω * Real.log (condEx p x f ω)) =
      Ex p (fun ω => f ω * Real.log (f ω / condEx p x f ω)) := by
  have hfxpos : ∀ ω, 0 < condEx p x f ω := condEx_pos h0 h1 x hf
  have hpull : Ex p (fun ω => condEx p x f ω * Real.log (condEx p x f ω)) =
      Ex p (fun ω => f ω * Real.log (condEx p x f ω)) := by
    rw [Ex_mul_fiberconst h0 h1 x f (fun ω => Real.log (condEx p x f ω))
      (fun ω t => by
        show Real.log (condEx p x f (Function.update ω x t)) =
          Real.log (condEx p x f ω)
        rw [condEx_apply_update])]
  rw [hpull]
  unfold Ex
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [Real.log_div (ne_of_gt (hf ω)) (ne_of_gt (hfxpos ω))]
  ring

/-- Per-coordinate generalized-tensorization step (Klein–Rio (2.3)):
`Ex[f log(f/E_x f)] ≤ Ex[g log(g/E_x g)] + Ex[(f−g) log(f/E_x f)]`. -/
theorem kr_percoord {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (f : (κ → Bool) → ℝ) (hf : ∀ ω, 0 < f ω) (x : κ)
    (g : (κ → Bool) → ℝ) (hg : ∀ ω, 0 < g ω) :
    Ex p (fun ω => f ω * Real.log (f ω / condEx p x f ω)) ≤
      Ex p (fun ω => g ω * Real.log (g ω / condEx p x g ω)) +
        Ex p (fun ω => (f ω - g ω) * Real.log (f ω / condEx p x f ω)) := by
  have hfxpos : ∀ ω, 0 < condEx p x f ω := condEx_pos h0 h1 x hf
  have hsplit : Ex p (fun ω => f ω * Real.log (f ω / condEx p x f ω)) =
      Ex p (fun ω => g ω * Real.log (f ω / condEx p x f ω)) +
        Ex p (fun ω => (f ω - g ω) * Real.log (f ω / condEx p x f ω)) := by
    rw [← Ex_add]
    exact Ex_congr fun ω => by ring
  rw [hsplit]
  have hgibbs : Ex p (fun ω => g ω * Real.log (f ω / condEx p x f ω)) ≤
      Ex p (fun ω => g ω * Real.log (g ω / condEx p x g ω)) := by
    rw [← Ex_condEx h0 h1 x (fun ω => g ω * Real.log (f ω / condEx p x f ω)),
      ← Ex_condEx h0 h1 x (fun ω => g ω * Real.log (g ω / condEx p x g ω))]
    apply Ex_mono h0 h1
    intro ω
    apply fiber_gibbs h0 h1 x g
      (fun ω' => Real.log (f ω' / condEx p x f ω')) hg ω
    have hexp : ∀ ω', Real.exp (Real.log (f ω' / condEx p x f ω')) =
        f ω' / condEx p x f ω' := fun ω' =>
      Real.exp_log (div_pos (hf ω') (hfxpos ω'))
    have hfun : (fun ω' => Real.exp (Real.log (f ω' / condEx p x f ω'))) =
        (fun ω' => f ω' / condEx p x f ω') := funext hexp
    rw [hfun]
    have hdiv : condEx p x (fun ω' => f ω' / condEx p x f ω') ω =
        condEx p x f ω / condEx p x f ω := by
      have := condEx_mul_fiberconst p x f
        (fun ω' => (condEx p x f ω')⁻¹)
        (fun ω' t => by
          show (condEx p x f (Function.update ω' x t))⁻¹ =
            (condEx p x f ω')⁻¹
          rw [condEx_apply_update]) ω
      simp only [div_eq_mul_inv]
      rw [this]
    rw [hdiv, div_self (ne_of_gt (hfxpos ω))]
  linarith [hgibbs]

/-- **Klein–Rio Proposition 2.1** (generalized tensorization), sum-land. -/
theorem kr_prop21 (p : NNReal) (hp : p ≤ 1)
    (f : (κ → Bool) → ℝ) (hf : ∀ ω, 0 < f ω)
    (g : κ → (κ → Bool) → ℝ) (hg : ∀ x ω, 0 < g x ω) :
    Ex (p : ℝ) (fun ω => f ω * Real.log (f ω)) -
      Ex (p : ℝ) f * Real.log (Ex (p : ℝ) f) ≤
      ∑ x : κ,
        (Ex (p : ℝ) (fun ω => g x ω * Real.log (g x ω / condEx (p : ℝ) x (g x) ω)) +
          Ex (p : ℝ) (fun ω => (f ω - g x ω) *
            Real.log (f ω / condEx (p : ℝ) x f ω))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have htensor := entropy_tensor_log p hp f hf
  refine le_trans htensor (Finset.sum_le_sum fun x _ => ?_)
  -- Per-x: Ex[f log f] − Ex[(condEx f)log(condEx f)] = Ex[f·log(f/condEx f)]
  have hfxpos : ∀ ω, 0 < condEx (p : ℝ) x f ω := condEx_pos h0p h1p x hf
  have hid : Ex (p : ℝ) (fun ω => f ω * Real.log (f ω)) -
      Ex (p : ℝ) (fun ω => condEx (p : ℝ) x f ω * Real.log (condEx (p : ℝ) x f ω)) =
      Ex (p : ℝ) (fun ω => f ω * Real.log (f ω / condEx (p : ℝ) x f ω)) := by
    have hpull : Ex (p : ℝ) (fun ω => condEx (p : ℝ) x f ω *
          Real.log (condEx (p : ℝ) x f ω)) =
        Ex (p : ℝ) (fun ω => f ω * Real.log (condEx (p : ℝ) x f ω)) := by
      rw [Ex_mul_fiberconst h0p h1p x f
        (fun ω => Real.log (condEx (p : ℝ) x f ω))
        (fun ω t => by
          show Real.log (condEx (p : ℝ) x f (Function.update ω x t)) =
            Real.log (condEx (p : ℝ) x f ω)
          rw [condEx_apply_update])]
    rw [hpull]
    unfold Ex
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [Real.log_div (ne_of_gt (hf ω)) (ne_of_gt (hfxpos ω))]
    ring
  rw [hid]
  -- Split f = g + (f − g) and bound the g-part by fiber Gibbs.
  have hsplit : Ex (p : ℝ) (fun ω => f ω * Real.log (f ω / condEx (p : ℝ) x f ω)) =
      Ex (p : ℝ) (fun ω => g x ω * Real.log (f ω / condEx (p : ℝ) x f ω)) +
        Ex (p : ℝ) (fun ω => (f ω - g x ω) *
          Real.log (f ω / condEx (p : ℝ) x f ω)) := by
    rw [← Ex_add]
    exact Ex_congr fun ω => by ring
  rw [hsplit]
  have hgibbs : Ex (p : ℝ) (fun ω => g x ω * Real.log (f ω / condEx (p : ℝ) x f ω)) ≤
      Ex (p : ℝ) (fun ω => g x ω * Real.log (g x ω / condEx (p : ℝ) x (g x) ω)) := by
    rw [← Ex_condEx h0p h1p x (fun ω => g x ω * Real.log (f ω / condEx (p : ℝ) x f ω)),
      ← Ex_condEx h0p h1p x (fun ω => g x ω * Real.log (g x ω / condEx (p : ℝ) x (g x) ω))]
    apply Ex_mono h0p h1p
    intro ω
    apply fiber_gibbs h0p h1p x (g x)
      (fun ω' => Real.log (f ω' / condEx (p : ℝ) x f ω')) (hg x) ω
    -- condEx e^{log(f/condEx f)} = condEx (f/condEx f) = 1 on the fiber.
    have hexp : ∀ ω', Real.exp (Real.log (f ω' / condEx (p : ℝ) x f ω')) =
        f ω' / condEx (p : ℝ) x f ω' := fun ω' =>
      Real.exp_log (div_pos (hf ω') (hfxpos ω'))
    have hfun : (fun ω' => Real.exp (Real.log (f ω' / condEx (p : ℝ) x f ω'))) =
        (fun ω' => f ω' / condEx (p : ℝ) x f ω') := funext hexp
    rw [hfun]
    -- condEx (f / C) = (condEx f)/C for fiber-constant positive C, = 1 at C = condEx f
    have hdiv : condEx (p : ℝ) x (fun ω' => f ω' / condEx (p : ℝ) x f ω') ω =
        condEx (p : ℝ) x f ω / condEx (p : ℝ) x f ω := by
      have := condEx_mul_fiberconst (p : ℝ) x f
        (fun ω' => (condEx (p : ℝ) x f ω')⁻¹)
        (fun ω' t => by
          show (condEx (p : ℝ) x f (Function.update ω' x t))⁻¹ =
            (condEx (p : ℝ) x f ω')⁻¹
          rw [condEx_apply_update]) ω
      simp only [div_eq_mul_inv]
      rw [this]
    rw [hdiv, div_self (ne_of_gt (hfxpos ω))]
  linarith [hgibbs]

end TalagrandCore
end

/-! ## Component: KRProcess -/
section
/-
Klein–Rio machinery, part 3: the exponentially compensated process.

  krComp t ω = max_a (t·S_a(ω) + L_a(t)),   krf = e^{−krComp},   krF = Ex krf.

Contents:
* canonical argmax `argmaxFun` (a function of the branch-value function, so
  fiber-constant branch data gives fiber-constant argmax);
* branch bounds, leave-one-out versions, and their fiber constancy;
* Lemma 4.2: `condEx x krf ≤ e^{−krCompErase} ≤ krf·e^{krEta}` with
  `e^{krEta} ≤ ψ(t) = (e^{2t}+1)/2`;
* `∑_x krEta = krComp = −log krf` (the telescoping identity);
* Lemma 4.1 facts: `krF ≤ 1`, `krF ≤ Ex e^{−tZ}`, `Ex e^{−tZ} ≤ krF·e^{max_a L_a}`;
* the frozen-branch comparison `krFrozen` with `krF s ≤ krFrozen t s`,
  `krFrozen t t = krF t`, `HasDerivAt (krFrozen t) (krFrozenD t) t` and
  `t·krFrozenD t ≤ Ex[krf log krf]` — the derivative interface for the
  differential-inequality integration (no a.e. derivatives of `krF` needed).
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-! ### Canonical argmax -/

/-- Canonical argmax over a nonempty fintype, as a function of the values. -/
noncomputable def argmaxFun (F : ι → ℝ) : ι :=
  Classical.choose (Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) F)

theorem argmaxFun_spec (F : ι → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty F = F (argmaxFun F) :=
  (Classical.choose_spec
    (Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) F)).2

/-! ### The compensated process -/

/-- `M_t(ω) = max_a (t·S_a(ω) + L_a(t))`. -/
noncomputable def krComp (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => t * linSum coeff p a ω + krL coeff p a t)

/-- `f_t = e^{−M_t}`. -/
noncomputable def krf (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (ω : κ → Bool) : ℝ :=
  Real.exp (-(krComp coeff p t ω))

/-- `F(t) = Ex f_t`. -/
noncomputable def krF (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) : ℝ :=
  Ex p (krf coeff p t)

/-- The (first) argmax branch. -/
noncomputable def krTau (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (ω : κ → Bool) : ι :=
  argmaxFun (fun a : ι => t * linSum coeff p a ω + krL coeff p a t)

theorem krComp_branch_le (coeff : ι → κ → ℝ) (p t : ℝ) (ω : κ → Bool) (a : ι) :
    t * linSum coeff p a ω + krL coeff p a t ≤ krComp coeff p t ω :=
  Finset.le_sup' (f := fun a : ι => t * linSum coeff p a ω + krL coeff p a t)
    (Finset.mem_univ a)

theorem krComp_tau (coeff : ι → κ → ℝ) (p t : ℝ) (ω : κ → Bool) :
    krComp coeff p t ω =
      t * linSum coeff p (krTau coeff p t ω) ω + krL coeff p (krTau coeff p t ω) t :=
  argmaxFun_spec _

theorem krf_pos (coeff : ι → κ → ℝ) (p t : ℝ) (ω : κ → Bool) :
    0 < krf coeff p t ω := Real.exp_pos _

theorem krf_le_branch (coeff : ι → κ → ℝ) (p t : ℝ) (ω : κ → Bool) (a : ι) :
    krf coeff p t ω ≤ Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) :=
  Real.exp_le_exp.mpr (neg_le_neg (krComp_branch_le coeff p t ω a))

theorem krF_pos {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ) (t : ℝ) :
    0 < krF coeff p t :=
  Ex_pos h0 h1 fun ω => krf_pos coeff p t ω

theorem log_krf (coeff : ι → κ → ℝ) (p t : ℝ) (ω : κ → Bool) :
    Real.log (krf coeff p t ω) = -(krComp coeff p t ω) := Real.log_exp _

/-! ### Leave-one-out versions -/

/-- `S_a` without coordinate `x`. -/
noncomputable def linSumErase (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ)
    (ω : κ → Bool) : ℝ :=
  ∑ y ∈ Finset.univ.erase x, linSummand coeff p a y (ω y)

/-- `L_a` without coordinate `x`. -/
noncomputable def krLErase (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  ∑ y ∈ Finset.univ.erase x, krl coeff p a y t

/-- Leave-one-out compensated maximum. -/
noncomputable def krCompErase (coeff : ι → κ → ℝ) (p : ℝ) (x : κ) (t : ℝ)
    (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => t * linSumErase coeff p a x ω + krLErase coeff p a x t)

/-- Leave-one-out argmax. -/
noncomputable def krTauE (coeff : ι → κ → ℝ) (p : ℝ) (x : κ) (t : ℝ)
    (ω : κ → Bool) : ι :=
  argmaxFun (fun a : ι => t * linSumErase coeff p a x ω + krLErase coeff p a x t)

theorem linSum_split (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (ω : κ → Bool) :
    linSum coeff p a ω = linSumErase coeff p a x ω + linSummand coeff p a x (ω x) := by
  unfold linSum linSumErase
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  ring

theorem krL_split (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) :
    krL coeff p a t = krLErase coeff p a x t + krl coeff p a x t := by
  unfold krL krLErase
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  ring

theorem linSumErase_update (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ)
    (ω : κ → Bool) (b : Bool) :
    linSumErase coeff p a x (Function.update ω x b) = linSumErase coeff p a x ω := by
  unfold linSumErase
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hy)]

theorem krTauE_update (coeff : ι → κ → ℝ) (p : ℝ) (x : κ) (t : ℝ)
    (ω : κ → Bool) (b : Bool) :
    krTauE coeff p x t (Function.update ω x b) = krTauE coeff p x t ω := by
  unfold krTauE
  congr 1
  funext a
  rw [linSumErase_update]

theorem krCompErase_update (coeff : ι → κ → ℝ) (p : ℝ) (x : κ) (t : ℝ)
    (ω : κ → Bool) (b : Bool) :
    krCompErase coeff p x t (Function.update ω x b) = krCompErase coeff p x t ω := by
  unfold krCompErase
  congr 1
  funext a
  rw [linSumErase_update]

theorem krCompErase_branch_le (coeff : ι → κ → ℝ) (p : ℝ) (x : κ) (t : ℝ)
    (ω : κ → Bool) (a : ι) :
    t * linSumErase coeff p a x ω + krLErase coeff p a x t ≤
      krCompErase coeff p x t ω :=
  Finset.le_sup'
    (f := fun a : ι => t * linSumErase coeff p a x ω + krLErase coeff p a x t)
    (Finset.mem_univ a)

theorem krCompErase_tauE (coeff : ι → κ → ℝ) (p : ℝ) (x : κ) (t : ℝ) (ω : κ → Bool) :
    krCompErase coeff p x t ω =
      t * linSumErase coeff p (krTauE coeff p x t ω) x ω +
        krLErase coeff p (krTauE coeff p x t ω) x t :=
  argmaxFun_spec _

/-! ### Lemma 4.2 -/

/-- First half of Lemma 4.2: `E_x f_t ≤ e^{−krCompErase}`. -/
theorem condEx_krf_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (x : κ) (t : ℝ) (ω : κ → Bool) :
    condEx p x (krf coeff p t) ω ≤ Real.exp (-(krCompErase coeff p x t ω)) := by
  set a' := krTauE coeff p x t ω with ha'
  -- pointwise on the fiber
  have hpt : ∀ b : Bool, krf coeff p t (Function.update ω x b) ≤
      Real.exp (-(krCompErase coeff p x t ω)) *
        Real.exp (-(t * linSummand coeff p a' x b + krl coeff p a' x t)) := by
    intro b
    have hbr := krf_le_branch coeff p t (Function.update ω x b) a'
    have hsplit : t * linSum coeff p a' (Function.update ω x b) + krL coeff p a' t =
        (t * linSumErase coeff p a' x ω + krLErase coeff p a' x t) +
          (t * linSummand coeff p a' x b + krl coeff p a' x t) := by
      rw [linSum_split coeff p a' x, krL_split coeff p a' x,
        linSumErase_update, Function.update_self]
      ring
    have herase : t * linSumErase coeff p a' x ω + krLErase coeff p a' x t =
        krCompErase coeff p x t ω := (krCompErase_tauE coeff p x t ω).symm
    rw [hsplit, herase] at hbr
    rw [← Real.exp_add]
    convert hbr using 2
    ring
  -- average over the fiber
  have hbt := bw_nonneg h0 h1 true
  have hbf := bw_nonneg h0 h1 false
  have m1 := mul_le_mul_of_nonneg_left (hpt true) hbt
  have m2 := mul_le_mul_of_nonneg_left (hpt false) hbf
  have hM : bw p true * Real.exp (-(t * linSummand coeff p a' x true + krl coeff p a' x t)) +
      bw p false * Real.exp (-(t * linSummand coeff p a' x false + krl coeff p a' x t)) = 1 := by
    have hexp : ∀ b : Bool,
        Real.exp (-(t * linSummand coeff p a' x b + krl coeff p a' x t)) =
          Real.exp (-(t * linSummand coeff p a' x b)) *
            Real.exp (-(krl coeff p a' x t)) := by
      intro b
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp true, hexp false]
    have hMpos := krM_pos h0 h1 coeff a' x t
    have hkrM : bw p true * Real.exp (-(t * linSummand coeff p a' x true)) +
        bw p false * Real.exp (-(t * linSummand coeff p a' x false)) =
        krM coeff p a' x t := rfl
    have hexplog : Real.exp (-(krl coeff p a' x t)) = (krM coeff p a' x t)⁻¹ := by
      rw [krl, Real.exp_neg, Real.exp_log hMpos]
    calc bw p true * (Real.exp (-(t * linSummand coeff p a' x true)) *
          Real.exp (-(krl coeff p a' x t))) +
        bw p false * (Real.exp (-(t * linSummand coeff p a' x false)) *
          Real.exp (-(krl coeff p a' x t))) =
        (bw p true * Real.exp (-(t * linSummand coeff p a' x true)) +
          bw p false * Real.exp (-(t * linSummand coeff p a' x false))) *
          Real.exp (-(krl coeff p a' x t)) := by ring
      _ = krM coeff p a' x t * (krM coeff p a' x t)⁻¹ := by rw [hkrM, hexplog]
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hMpos)
  show bw p true * krf coeff p t (Function.update ω x true) +
      bw p false * krf coeff p t (Function.update ω x false) ≤
      Real.exp (-(krCompErase coeff p x t ω))
  calc bw p true * krf coeff p t (Function.update ω x true) +
      bw p false * krf coeff p t (Function.update ω x false) ≤
      bw p true * (Real.exp (-(krCompErase coeff p x t ω)) *
        Real.exp (-(t * linSummand coeff p a' x true + krl coeff p a' x t))) +
      bw p false * (Real.exp (-(krCompErase coeff p x t ω)) *
        Real.exp (-(t * linSummand coeff p a' x false + krl coeff p a' x t))) :=
        add_le_add m1 m2
    _ = Real.exp (-(krCompErase coeff p x t ω)) *
        (bw p true * Real.exp (-(t * linSummand coeff p a' x true + krl coeff p a' x t)) +
         bw p false * Real.exp (-(t * linSummand coeff p a' x false + krl coeff p a' x t))) := by
        ring
    _ = Real.exp (-(krCompErase coeff p x t ω)) := by rw [hM, mul_one]

/-- The per-coordinate active-branch exponent `η_x = t·s_{x,τ}(ω_x) + l_{x,τ}(t)`. -/
noncomputable def krEta (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (x : κ) (ω : κ → Bool) : ℝ :=
  t * linSummand coeff p (krTau coeff p t ω) x (ω x) +
    krl coeff p (krTau coeff p t ω) x t

/-- Second half of Lemma 4.2: `e^{−krCompErase} ≤ f_t·e^{η_x}`. -/
theorem exp_neg_compErase_le (coeff : ι → κ → ℝ) (p : ℝ) (x : κ) (t : ℝ)
    (ω : κ → Bool) :
    Real.exp (-(krCompErase coeff p x t ω)) ≤
      krf coeff p t ω * Real.exp (krEta coeff p t x ω) := by
  set τ := krTau coeff p t ω with hτ
  have hbr := krCompErase_branch_le coeff p x t ω τ
  have hsplit : t * linSumErase coeff p τ x ω + krLErase coeff p τ x t =
      krComp coeff p t ω - krEta coeff p t x ω := by
    have h1 := linSum_split coeff p τ x ω
    have h2 := krL_split coeff p τ x t
    have h3 := krComp_tau coeff p t ω
    unfold krEta
    rw [← hτ, h3, h1, h2]
    ring
  rw [hsplit] at hbr
  unfold krf
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Combined Lemma 4.2: `E_x f_t ≤ f_t·e^{η_x}`. -/
theorem condEx_krf_le_mul {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (x : κ) (t : ℝ) (ω : κ → Bool) :
    condEx p x (krf coeff p t) ω ≤
      krf coeff p t ω * Real.exp (krEta coeff p t x ω) :=
  le_trans (condEx_krf_le h0 h1 coeff x t ω) (exp_neg_compErase_le coeff p x t ω)

/-- `e^{η_x} ≤ ψ(t) = (e^{2t}+1)/2` (needs `|coeff| ≤ 1`, `t ≥ 0`). -/
theorem exp_krEta_le_psi {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    (hB : ∀ a x, |coeff a x| ≤ 1) (x : κ) {t : ℝ} (ht : 0 ≤ t) (ω : κ → Bool) :
    Real.exp (krEta coeff p t x ω) ≤ (Real.exp (2 * t) + 1) / 2 := by
  set τ := krTau coeff p t ω with hτ
  unfold krEta
  rw [← hτ, Real.exp_add]
  have h1' : Real.exp (t * linSummand coeff p τ x (ω x)) ≤ Real.exp t := by
    apply Real.exp_le_exp.mpr
    have habs := linSummand_abs_le h0 h1 (hB τ x) (ω x)
    have := (abs_le.mp habs).2
    nlinarith
  have h2' : Real.exp (krl coeff p τ x t) ≤ (Real.exp t + Real.exp (-t)) / 2 := by
    rw [krl, Real.exp_log (krM_pos h0 h1 coeff τ x t)]
    exact krM_le_cosh h0 h1 (hB τ x) t
  have hcosh_pos : (0:ℝ) < (Real.exp t + Real.exp (-t)) / 2 := by positivity
  calc Real.exp (t * linSummand coeff p τ x (ω x)) * Real.exp (krl coeff p τ x t) ≤
      Real.exp t * ((Real.exp t + Real.exp (-t)) / 2) := by
        apply mul_le_mul h1' h2' (Real.exp_pos _).le (Real.exp_pos _).le
    _ = (Real.exp (2 * t) + 1) / 2 := by
        rw [show (2:ℝ) * t = t + t from by ring, Real.exp_add]
        have : Real.exp t * Real.exp (-t) = 1 := by
          rw [← Real.exp_add]; simp
        nlinarith [this]

/-- `η_x ≤ log ψ(t)`. -/
theorem krEta_le_log_psi {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    (hB : ∀ a x, |coeff a x| ≤ 1) (x : κ) {t : ℝ} (ht : 0 ≤ t) (ω : κ → Bool) :
    krEta coeff p t x ω ≤ Real.log ((Real.exp (2 * t) + 1) / 2) := by
  have h := exp_krEta_le_psi h0 h1 hB x ht ω
  have := Real.log_le_log (Real.exp_pos _) h
  rwa [Real.log_exp] at this

/-- Telescoping: `∑_x η_x = krComp = −log f_t`. -/
theorem sum_krEta (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (ω : κ → Bool) :
    ∑ x : κ, krEta coeff p t x ω = krComp coeff p t ω := by
  unfold krEta
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [krComp_tau coeff p t ω]
  rfl

/-! ### Lemma 4.1 facts -/

theorem krF_le_one {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ) (t : ℝ) :
    krF coeff p t ≤ 1 := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty ι)
  have hpt : ∀ ω, krf coeff p t ω ≤
      Real.exp (-(krL coeff p a₀ t)) * Real.exp (-(t * linSum coeff p a₀ ω)) := by
    intro ω
    have := krf_le_branch coeff p t ω a₀
    rw [← Real.exp_add]
    convert this using 2
    ring
  calc krF coeff p t ≤ Ex p (fun ω =>
        Real.exp (-(krL coeff p a₀ t)) * Real.exp (-(t * linSum coeff p a₀ ω))) :=
        Ex_mono h0 h1 hpt
    _ = Real.exp (-(krL coeff p a₀ t)) *
        Ex p (fun ω => Real.exp (-(t * linSum coeff p a₀ ω))) := Ex_smul _ _
    _ = 1 := by
        rw [Ex_exp_neg_linSum]
        rw [show (∏ x : κ, krM coeff p a₀ x t) =
            Real.exp (krL coeff p a₀ t) from ?_]
        · rw [← Real.exp_add]; simp
        · rw [krL, Real.exp_sum]
          exact Finset.prod_congr rfl fun x _ =>
            (Real.exp_log (krM_pos h0 h1 coeff a₀ x t)).symm

/-- `f_t ≤ e^{−tZ}` pointwise (`t ≥ 0`), hence `krF ≤ Ex e^{−tZ}`. -/
theorem krf_le_exp_neg_tZ {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ω : κ → Bool) :
    krf coeff p t ω ≤ Real.exp (-(t * Zproc coeff p ω)) := by
  obtain ⟨a, ha⟩ := supProc_exists_argmax (linSummand coeff p) ω
  have hZ : Zproc coeff p ω = linSum coeff p a ω := ha
  have hL := krL_nonneg h0 h1 coeff a t
  calc krf coeff p t ω ≤ Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) :=
        krf_le_branch coeff p t ω a
    _ ≤ Real.exp (-(t * Zproc coeff p ω)) := by
        apply Real.exp_le_exp.mpr
        rw [hZ]
        linarith

theorem krF_le_Ex_exp_neg_tZ {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    krF coeff p t ≤ Ex p (fun ω => Real.exp (-(t * Zproc coeff p ω))) :=
  Ex_mono h0 h1 (krf_le_exp_neg_tZ h0 h1 coeff ht)

/-- Transfer: `Ex e^{−tZ} ≤ krF·e^{max_a L_a}` (`t ≥ 0`). -/
theorem Ex_exp_neg_tZ_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    Ex p (fun ω => Real.exp (-(t * Zproc coeff p ω))) ≤
      krF coeff p t *
        Real.exp (Finset.univ.sup' Finset.univ_nonempty
          (fun a : ι => krL coeff p a t)) := by
  set Lmax := Finset.univ.sup' Finset.univ_nonempty (fun a : ι => krL coeff p a t)
    with hLmax
  have hpt : ∀ ω, Real.exp (-(t * Zproc coeff p ω)) ≤
      krf coeff p t ω * Real.exp Lmax := by
    intro ω
    have hcomp : krComp coeff p t ω ≤ t * Zproc coeff p ω + Lmax := by
      apply Finset.sup'_le
      intro a _
      have h1' : linSum coeff p a ω ≤ Zproc coeff p ω :=
        le_supProc (linSummand coeff p) ω a
      have h2' : krL coeff p a t ≤ Lmax :=
        Finset.le_sup' (f := fun a : ι => krL coeff p a t) (Finset.mem_univ a)
      have h3' : t * linSum coeff p a ω ≤ t * Zproc coeff p ω :=
        mul_le_mul_of_nonneg_left h1' ht
      linarith
    unfold krf
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  calc Ex p (fun ω => Real.exp (-(t * Zproc coeff p ω))) ≤
      Ex p (fun ω => krf coeff p t ω * Real.exp Lmax) := Ex_mono h0 h1 hpt
    _ = krF coeff p t * Real.exp Lmax := by
        rw [show (fun ω => krf coeff p t ω * Real.exp Lmax) =
            (fun ω => Real.exp Lmax * krf coeff p t ω) from
            funext fun ω => by ring]
        rw [Ex_smul, mul_comm]
        rfl

/-! ### The frozen-branch comparison (derivative interface) -/

/-- Branches frozen at the time-`t` argmax, evaluated at time `s`. -/
noncomputable def krFrozen (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (s : ℝ) : ℝ :=
  Ex p (fun ω => Real.exp (-(s * linSum coeff p (krTau coeff p t ω) ω +
    krL coeff p (krTau coeff p t ω) s)))

/-- Its derivative at `s = t`. -/
noncomputable def krFrozenD (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) : ℝ :=
  Ex p (fun ω => -(linSum coeff p (krTau coeff p t ω) ω +
    krLd coeff p (krTau coeff p t ω) t) * krf coeff p t ω)

theorem krF_le_krFrozen {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t s : ℝ) : krF coeff p s ≤ krFrozen coeff p t s :=
  Ex_mono h0 h1 fun ω => krf_le_branch coeff p s ω (krTau coeff p t ω)

theorem krFrozen_self (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) :
    krFrozen coeff p t t = krF coeff p t :=
  Ex_congr fun ω => by
    rw [krf, krComp_tau coeff p t ω]

theorem hasDerivAt_krFrozen {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t : ℝ) : HasDerivAt (krFrozen coeff p t) (krFrozenD coeff p t) t := by
  unfold krFrozen krFrozenD Ex
  have hterm : ∀ ω : κ → Bool,
      HasDerivAt (fun s : ℝ => W p ω * Real.exp (-(s * linSum coeff p (krTau coeff p t ω) ω +
        krL coeff p (krTau coeff p t ω) s)))
      (W p ω * (-(linSum coeff p (krTau coeff p t ω) ω +
        krLd coeff p (krTau coeff p t ω) t) * krf coeff p t ω)) t := by
    intro ω
    set τ := krTau coeff p t ω
    set A := linSum coeff p τ ω
    have hlin : HasDerivAt (fun s : ℝ => s * A) A t := by
      simpa using (hasDerivAt_id t).mul_const A
    have hsum : HasDerivAt (fun s : ℝ => s * A + krL coeff p τ s)
        (A + krLd coeff p τ t) t := hlin.add (hasDerivAt_krL h0 h1 coeff τ t)
    have hneg : HasDerivAt (fun s : ℝ => -(s * A + krL coeff p τ s))
        (-(A + krLd coeff p τ t)) t := hsum.neg
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(s * A + krL coeff p τ s)))
        (Real.exp (-(t * A + krL coeff p τ t)) * -(A + krLd coeff p τ t)) t :=
      hneg.exp
    have hres : HasDerivAt
        (fun s : ℝ => W p ω * Real.exp (-(s * A + krL coeff p τ s)))
        (W p ω * (Real.exp (-(t * A + krL coeff p τ t)) * -(A + krLd coeff p τ t))) t :=
      hexp.const_mul (W p ω)
    convert hres using 1
    unfold krf
    rw [krComp_tau coeff p t ω]
    ring
  have h := HasDerivAt.sum
    (fun ω (_ : ω ∈ (Finset.univ : Finset (κ → Bool))) => hterm ω)
  have hfun : (∑ ω : κ → Bool, fun s : ℝ =>
      W p ω * Real.exp (-(s * linSum coeff p (krTau coeff p t ω) ω +
        krL coeff p (krTau coeff p t ω) s))) =
      fun s : ℝ => ∑ ω : κ → Bool,
        W p ω * Real.exp (-(s * linSum coeff p (krTau coeff p t ω) ω +
          krL coeff p (krTau coeff p t ω) s)) := by
    funext s
    exact Finset.sum_apply s Finset.univ _
  rw [hfun] at h
  exact h

/-- The key derivative bound: `t·krFrozenD t ≤ Ex[f_t·log f_t]`. -/
theorem krFrozenD_mul_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    t * krFrozenD coeff p t ≤
      Ex p (fun ω => krf coeff p t ω * Real.log (krf coeff p t ω)) := by
  unfold krFrozenD
  rw [← Ex_smul]
  apply Ex_mono h0 h1
  intro ω
  set τ := krTau coeff p t ω
  have hlog : Real.log (krf coeff p t ω) = -(t * linSum coeff p τ ω + krL coeff p τ t) := by
    rw [log_krf, krComp_tau coeff p t ω]
  have hdev := krL_tderiv_sub_nonneg h0 h1 coeff τ t
  have hf := (krf_pos coeff p t ω).le
  rw [hlog]
  have hexpand : t * (-(linSum coeff p τ ω + krLd coeff p τ t) * krf coeff p t ω) =
      (-(t * linSum coeff p τ ω + krL coeff p τ t)) * krf coeff p t ω -
        (t * krLd coeff p τ t - krL coeff p τ t) * krf coeff p t ω := by
    ring
  rw [hexpand]
  have hsub : 0 ≤ (t * krLd coeff p τ t - krL coeff p τ t) * krf coeff p t ω :=
    mul_nonneg hdev hf
  linarith

end TalagrandCore
end

/-! ## Component: KREntropy -/
section
/-
Klein–Rio machinery, part 4: the entropy differential inequality at fixed time
(their (4.8)–(4.21), F′-free formulation).

Main result `kr_entropy_master`: for 0 < t with ϕ(t) := ψ(t)·log ψ(t) ≤ 1,

  Ex[f_t log f_t] − (1 − ϕ(t))·F·log F ≤ ψ(t)·σ²·(1+(t−1)eᵗ)·F,

where f_t is the compensated `krf`, F = krF, ψ(t) = (e^{2t}+1)/2.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-! ### Argmax indicators -/

open Classical in
/-- Indicator of the event `krTau = a`. -/
noncomputable def krInd (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (a : ι)
    (ω : κ → Bool) : ℝ :=
  if krTau coeff p t ω = a then 1 else 0

theorem krInd_nonneg (coeff : ι → κ → ℝ) (p t : ℝ) (a : ι) (ω : κ → Bool) :
    0 ≤ krInd coeff p t a ω := by
  unfold krInd
  split <;> norm_num

theorem sum_krInd_mul (coeff : ι → κ → ℝ) (p t : ℝ) (ω : κ → Bool) (H : ι → ℝ) :
    ∑ a : ι, krInd coeff p t a ω * H a = H (krTau coeff p t ω) := by
  rw [Finset.sum_eq_single (krTau coeff p t ω)]
  · unfold krInd
    rw [if_pos rfl, one_mul]
  · intro b _ hb
    unfold krInd
    rw [if_neg fun h => hb h.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_krInd (coeff : ι → κ → ℝ) (p t : ℝ) (ω : κ → Bool) :
    ∑ a : ι, krInd coeff p t a ω = 1 := by
  have := sum_krInd_mul coeff p t ω (fun _ => 1)
  simpa using this

theorem sum_condEx_krInd {p : ℝ} (coeff : ι → κ → ℝ) (t : ℝ) (x : κ)
    (ω : κ → Bool) :
    ∑ a : ι, condEx p x (krInd coeff p t a) ω = 1 := by
  unfold condEx
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_krInd, sum_krInd, mul_one, mul_one, bw_sum]

theorem condEx_krInd_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (coeff : ι → κ → ℝ) (t : ℝ) (a : ι) (x : κ) (ω : κ → Bool) :
    0 ≤ condEx p x (krInd coeff p t a) ω :=
  condEx_nonneg h0 h1 x (fun ω' => krInd_nonneg coeff p t a ω') ω

/-- `condEx x (krInd a)` is fiber-constant. -/
theorem condEx_krInd_fiberconst {p : ℝ} (coeff : ι → κ → ℝ) (t : ℝ) (a : ι)
    (x : κ) (ω : κ → Bool) (b : Bool) :
    condEx p x (krInd coeff p t a) (Function.update ω x b) =
      condEx p x (krInd coeff p t a) ω :=
  condEx_apply_update x _ ω b

/-! ### The auxiliary functions -/

/-- The `x`-erased branch weight `e^{−(t·S^x_a + L^x_a)}` (fiber-constant). -/
noncomputable def krC (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (x : κ) (a : ι)
    (ω : κ → Bool) : ℝ :=
  Real.exp (-(t * linSumErase coeff p a x ω + krLErase coeff p a x t))

theorem krC_pos (coeff : ι → κ → ℝ) (p t : ℝ) (x : κ) (a : ι) (ω : κ → Bool) :
    0 < krC coeff p t x a ω := Real.exp_pos _

theorem krC_fiberconst (coeff : ι → κ → ℝ) (p t : ℝ) (x : κ) (a : ι)
    (ω : κ → Bool) (b : Bool) :
    krC coeff p t x a (Function.update ω x b) = krC coeff p t x a ω := by
  unfold krC
  rw [linSumErase_update]

/-- `f_t·e^{η_x} = krC` at the argmax branch. -/
theorem krf_mul_exp_eta (coeff : ι → κ → ℝ) (p t : ℝ) (x : κ) (ω : κ → Bool) :
    krf coeff p t ω * Real.exp (krEta coeff p t x ω) =
      krC coeff p t x (krTau coeff p t ω) ω := by
  unfold krf krC krEta
  rw [← Real.exp_add]
  congr 1
  rw [krComp_tau coeff p t ω,
    linSum_split coeff p (krTau coeff p t ω) x ω,
    krL_split coeff p (krTau coeff p t ω) x t]
  ring

/-- The Klein–Rio auxiliary `g_x` ((4.9)). -/
noncomputable def krg (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (x : κ)
    (ω : κ → Bool) : ℝ :=
  ∑ a : ι, condEx p x (krInd coeff p t a) ω *
    Real.exp (-(t * linSum coeff p a ω + krL coeff p a t))

theorem krf_le_krg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t : ℝ) (x : κ) (ω : κ → Bool) :
    krf coeff p t ω ≤ krg coeff p t x ω := by
  unfold krg
  have hterm : ∀ a : ι,
      condEx p x (krInd coeff p t a) ω * krf coeff p t ω ≤
        condEx p x (krInd coeff p t a) ω *
          Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) := by
    intro a
    exact mul_le_mul_of_nonneg_left (krf_le_branch coeff p t ω a)
      (condEx_krInd_nonneg h0 h1 coeff t a x ω)
  calc krf coeff p t ω =
      (∑ a : ι, condEx p x (krInd coeff p t a) ω) * krf coeff p t ω := by
        rw [sum_condEx_krInd, one_mul]
    _ = ∑ a : ι, condEx p x (krInd coeff p t a) ω * krf coeff p t ω := by
        rw [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum fun a _ => hterm a

theorem krg_pos {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t : ℝ) (x : κ) (ω : κ → Bool) : 0 < krg coeff p t x ω :=
  lt_of_lt_of_le (krf_pos coeff p t ω) (krf_le_krg h0 h1 coeff t x ω)

/-! ### `condEx` computations -/

/-- The branch factor integrates to `krC` on the fiber. -/
theorem condEx_branch (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t : ℝ) (x : κ) (a : ι) (ω : κ → Bool) :
    condEx p x (fun ω' => Real.exp (-(t * linSum coeff p a ω' + krL coeff p a t))) ω =
      krC coeff p t x a ω := by
  unfold condEx
  have hpt : ∀ b : Bool,
      Real.exp (-(t * linSum coeff p a (Function.update ω x b) + krL coeff p a t)) =
        krC coeff p t x a ω *
          (Real.exp (-(t * linSummand coeff p a x b)) *
            Real.exp (-(krl coeff p a x t))) := by
    intro b
    unfold krC
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [linSum_split coeff p a x (Function.update ω x b),
      linSumErase_update, Function.update_self,
      krL_split coeff p a x t]
    ring
  have hM := krM_pos h0 h1 coeff a x t
  have hexplog : Real.exp (-(krl coeff p a x t)) * krM coeff p a x t = 1 := by
    rw [krl, Real.exp_neg, Real.exp_log hM]
    exact inv_mul_cancel₀ (ne_of_gt hM)
  have hkrM : bw p true * Real.exp (-(t * linSummand coeff p a x true)) +
      bw p false * Real.exp (-(t * linSummand coeff p a x false)) =
      krM coeff p a x t := rfl
  show bw p true * Real.exp (-(t * linSum coeff p a (Function.update ω x true) +
        krL coeff p a t)) +
      bw p false * Real.exp (-(t * linSum coeff p a (Function.update ω x false) +
        krL coeff p a t)) =
      krC coeff p t x a ω
  rw [hpt true, hpt false]
  calc bw p true * (krC coeff p t x a ω *
        (Real.exp (-(t * linSummand coeff p a x true)) *
          Real.exp (-(krl coeff p a x t)))) +
      bw p false * (krC coeff p t x a ω *
        (Real.exp (-(t * linSummand coeff p a x false)) *
          Real.exp (-(krl coeff p a x t)))) =
      krC coeff p t x a ω *
        ((bw p true * Real.exp (-(t * linSummand coeff p a x true)) +
          bw p false * Real.exp (-(t * linSummand coeff p a x false))) *
          Real.exp (-(krl coeff p a x t))) := by ring
    _ = krC coeff p t x a ω *
        (krM coeff p a x t * Real.exp (-(krl coeff p a x t))) := by rw [hkrM]
    _ = krC coeff p t x a ω := by
        rw [mul_comm (krM coeff p a x t), hexplog, mul_one]

/-- `condEx` commutes with finite sums. -/
theorem condEx_finsum {α : Type} (s : Finset α) (u : α → (κ → Bool) → ℝ)
    (p : ℝ) (x : κ) (ω : κ → Bool) :
    condEx p x (fun ω' => ∑ a ∈ s, u a ω') ω = ∑ a ∈ s, condEx p x (u a) ω := by
  show bw p true * (∑ a ∈ s, u a (Function.update ω x true)) +
      bw p false * (∑ a ∈ s, u a (Function.update ω x false)) =
      ∑ a ∈ s, condEx p x (u a) ω
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rfl

/-- `E_x g_x = ∑_a P_a·krC_a` (Klein–Rio (4.12)). -/
theorem condEx_krg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t : ℝ) (x : κ) (ω : κ → Bool) :
    condEx p x (krg coeff p t x) ω =
      ∑ a : ι, condEx p x (krInd coeff p t a) ω * krC coeff p t x a ω := by
  unfold krg
  rw [condEx_finsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hcomm : (fun ω' => condEx p x (krInd coeff p t a) ω' *
      Real.exp (-(t * linSum coeff p a ω' + krL coeff p a t))) =
      (fun ω' => Real.exp (-(t * linSum coeff p a ω' + krL coeff p a t)) *
        condEx p x (krInd coeff p t a) ω') := funext fun ω' => mul_comm _ _
  rw [hcomm, condEx_mul_fiberconst p x _ _
    (fun ω' b => condEx_apply_update x _ ω' b) ω,
    condEx_branch p h0 h1 coeff t x a ω]
  ring

/-- `Ex g_x = Ex (f_t·e^{η_x})` (Klein–Rio (4.13), left side). -/
theorem Ex_krg_eq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t : ℝ) (x : κ) :
    Ex p (krg coeff p t x) =
      Ex p (fun ω => krf coeff p t ω * Real.exp (krEta coeff p t x ω)) := by
  rw [← Ex_condEx h0 h1 x (krg coeff p t x)]
  rw [Ex_congr (condEx_krg h0 h1 coeff t x)]
  rw [Ex_finsum Finset.univ
    (fun a ω => condEx p x (krInd coeff p t a) ω * krC coeff p t x a ω)]
  have hper : ∀ a : ι,
      Ex p (fun ω => condEx p x (krInd coeff p t a) ω * krC coeff p t x a ω) =
        Ex p (fun ω => krInd coeff p t a ω * krC coeff p t x a ω) :=
    fun a => (Ex_mul_fiberconst h0 h1 x (krInd coeff p t a) (krC coeff p t x a)
      (fun ω b => krC_fiberconst coeff p t x a ω b)).symm
  rw [Finset.sum_congr rfl fun a _ => hper a]
  rw [← Ex_finsum Finset.univ
    (fun a ω => krInd coeff p t a ω * krC coeff p t x a ω)]
  refine Ex_congr fun ω => ?_
  rw [sum_krInd_mul coeff p t ω (fun a => krC coeff p t x a ω)]
  exact (krf_mul_exp_eta coeff p t x ω).symm

/-! ### Finite Jensen for `x log x` -/

theorem finset_xlogx_jensen {α : Type} [Fintype α] (μ v : α → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hsum : ∑ a : α, μ a = 1) (hv : ∀ a, 0 < v a) :
    (∑ a : α, μ a * v a) * Real.log (∑ a : α, μ a * v a) ≤
      ∑ a : α, μ a * (v a * Real.log (v a)) := by
  set m := ∑ a : α, μ a * v a with hm
  have hμv : ∀ a, 0 ≤ μ a * v a := fun a => mul_nonneg (hμ a) (hv a).le
  have hmpos : 0 < m := by
    have hex : ∃ a, 0 < μ a := by
      by_contra hno
      push_neg at hno
      have hz : ∀ a, μ a = 0 := fun a => le_antisymm (hno a) (hμ a)
      rw [Finset.sum_congr rfl (fun a _ => hz a), Finset.sum_const_zero] at hsum
      norm_num at hsum
    obtain ⟨a₀, ha₀⟩ := hex
    exact lt_of_lt_of_le (mul_pos ha₀ (hv a₀))
      (Finset.single_le_sum (fun a _ => hμv a) (Finset.mem_univ a₀))
  have key : ∀ a, μ a * v a * Real.log m ≤
      μ a * (v a * Real.log (v a)) + μ a * m - μ a * v a := by
    intro a
    have hlog := Real.log_le_sub_one_of_pos (div_pos hmpos (hv a))
    rw [Real.log_div (ne_of_gt hmpos) (ne_of_gt (hv a))] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (hμv a)
    have hfield : μ a * v a * (m / v a - 1) = μ a * m - μ a * v a := by
      have hva : v a ≠ 0 := ne_of_gt (hv a)
      field_simp
    nlinarith [hmul, hfield]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => key a)
  rw [← Finset.sum_mul] at hs
  have hrhs : ∑ a : α, (μ a * (v a * Real.log (v a)) + μ a * m - μ a * v a) =
      (∑ a : α, μ a * (v a * Real.log (v a))) + m - m := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hsum,
      one_mul]
  rw [hrhs] at hs
  linarith

/-! ### The A-term bound (Klein–Rio (4.16)–(4.17)) -/

/-- Pointwise Jensen step: `g_x·log(g_x/E_x g_x) ≤ ∑_a P_a·e^{−(tS_a+L_a)}·(−(t·s_ax + l_ax))`. -/
theorem krg_xlogx_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t : ℝ) (x : κ) (ω : κ → Bool) :
    krg coeff p t x ω *
        Real.log (krg coeff p t x ω / condEx p x (krg coeff p t x) ω) ≤
      ∑ a : ι, condEx p x (krInd coeff p t a) ω *
        (Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) *
          (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t))) := by
  set C := condEx p x (krg coeff p t x) ω with hCdef
  have hCpos : 0 < C :=
    condEx_pos h0 h1 x (krg_pos h0 h1 coeff t x) ω
  set μ : ι → ℝ := fun a =>
    condEx p x (krInd coeff p t a) ω * krC coeff p t x a ω / C with hμdef
  set v : ι → ℝ := fun a =>
    Real.exp (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t)) with hvdef
  have hμ : ∀ a, 0 ≤ μ a := fun a => by
    simp only [hμdef]
    exact div_nonneg (mul_nonneg (condEx_krInd_nonneg h0 h1 coeff t a x ω)
      (krC_pos coeff p t x a ω).le) hCpos.le
  have hv : ∀ a, 0 < v a := fun a => by
    simp only [hvdef]; exact Real.exp_pos _
  have hsumμ : ∑ a : ι, μ a = 1 := by
    simp only [hμdef]
    rw [← Finset.sum_div, ← condEx_krg h0 h1 coeff t x ω]
    exact div_self (ne_of_gt hCpos)
  have hCv : ∀ a, krC coeff p t x a ω * v a =
      Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) := by
    intro a
    simp only [hvdef]
    unfold krC
    rw [← Real.exp_add]
    congr 1
    rw [linSum_split coeff p a x ω, krL_split coeff p a x t]
    ring
  have hμv : ∑ a : ι, μ a * v a = krg coeff p t x ω / C := by
    have hper : ∀ a : ι, μ a * v a =
        condEx p x (krInd coeff p t a) ω *
          Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) / C := by
      intro a
      have : μ a * v a = condEx p x (krInd coeff p t a) ω *
          (krC coeff p t x a ω * v a) / C := by
        simp only [hμdef]; ring
      rw [this, hCv a]
    rw [Finset.sum_congr rfl (fun a _ => hper a), ← Finset.sum_div]
    rfl
  have hjensen := finset_xlogx_jensen μ v hμ hsumμ hv
  rw [hμv] at hjensen
  have hgoal := mul_le_mul_of_nonneg_left hjensen hCpos.le
  have hL : C * (krg coeff p t x ω / C * Real.log (krg coeff p t x ω / C)) =
      krg coeff p t x ω * Real.log (krg coeff p t x ω / C) := by
    field_simp
  have hR : C * ∑ a : ι, μ a * (v a * Real.log (v a)) =
      ∑ a : ι, condEx p x (krInd coeff p t a) ω *
        (Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) *
          (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hlogv : Real.log (v a) =
        -(t * linSummand coeff p a x (ω x) + krl coeff p a x t) := by
      simp only [hvdef]; exact Real.log_exp _
    have hexpand : C * (μ a * (v a * Real.log (v a))) =
        condEx p x (krInd coeff p t a) ω *
          ((krC coeff p t x a ω * v a) * Real.log (v a)) := by
      simp only [hμdef]
      field_simp
    rw [hexpand, hCv a, hlogv]
  rw [hL, hR] at hgoal
  exact hgoal

/-- `condEx` of the branch-weighted derivative integrand. -/
theorem condEx_G {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t : ℝ) (x : κ) (a : ι) (ω : κ → Bool) :
    condEx p x (fun ω' => Real.exp (-(t * linSum coeff p a ω' + krL coeff p a t)) *
      (-(t * linSummand coeff p a x (ω' x) + krl coeff p a x t))) ω =
      krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t) := by
  have hM := krM_pos h0 h1 coeff a x t
  have hpt : ∀ b : Bool,
      Real.exp (-(t * linSum coeff p a (Function.update ω x b) + krL coeff p a t)) *
        (-(t * linSummand coeff p a x ((Function.update ω x b) x) +
          krl coeff p a x t)) =
      krC coeff p t x a ω * (Real.exp (-(krl coeff p a x t)) *
        (Real.exp (-(t * linSummand coeff p a x b)) *
          (-(t * linSummand coeff p a x b) - krl coeff p a x t))) := by
    intro b
    have hbr : Real.exp (-(t * linSum coeff p a (Function.update ω x b) +
        krL coeff p a t)) =
        krC coeff p t x a ω * (Real.exp (-(t * linSummand coeff p a x b)) *
          Real.exp (-(krl coeff p a x t))) := by
      unfold krC
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [linSum_split coeff p a x (Function.update ω x b),
        linSumErase_update, Function.update_self,
        krL_split coeff p a x t]
      ring
    rw [hbr, Function.update_self]
    ring
  show bw p true * (Real.exp (-(t * linSum coeff p a (Function.update ω x true) +
        krL coeff p a t)) *
      (-(t * linSummand coeff p a x ((Function.update ω x true) x) +
        krl coeff p a x t))) +
    bw p false * (Real.exp (-(t * linSum coeff p a (Function.update ω x false) +
        krL coeff p a t)) *
      (-(t * linSummand coeff p a x ((Function.update ω x false) x) +
        krl coeff p a x t))) =
    krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t)
  rw [hpt true, hpt false]
  have hinner : bw p true * (Real.exp (-(t * linSummand coeff p a x true)) *
        (-(t * linSummand coeff p a x true) - krl coeff p a x t)) +
      bw p false * (Real.exp (-(t * linSummand coeff p a x false)) *
        (-(t * linSummand coeff p a x false) - krl coeff p a x t)) =
      t * krMd coeff p a x t - krl coeff p a x t * krM coeff p a x t := by
    unfold krMd krM
    ring
  have hexplog : Real.exp (-(krl coeff p a x t)) = (krM coeff p a x t)⁻¹ := by
    rw [krl, Real.exp_neg, Real.exp_log hM]
  have hkey : Real.exp (-(krl coeff p a x t)) *
      (t * krMd coeff p a x t - krl coeff p a x t * krM coeff p a x t) =
      t * krld coeff p a x t - krl coeff p a x t := by
    rw [hexplog]
    unfold krld
    field_simp
  calc bw p true * (krC coeff p t x a ω * (Real.exp (-(krl coeff p a x t)) *
        (Real.exp (-(t * linSummand coeff p a x true)) *
          (-(t * linSummand coeff p a x true) - krl coeff p a x t)))) +
      bw p false * (krC coeff p t x a ω * (Real.exp (-(krl coeff p a x t)) *
        (Real.exp (-(t * linSummand coeff p a x false)) *
          (-(t * linSummand coeff p a x false) - krl coeff p a x t)))) =
      krC coeff p t x a ω * (Real.exp (-(krl coeff p a x t)) *
        (bw p true * (Real.exp (-(t * linSummand coeff p a x true)) *
          (-(t * linSummand coeff p a x true) - krl coeff p a x t)) +
         bw p false * (Real.exp (-(t * linSummand coeff p a x false)) *
          (-(t * linSummand coeff p a x false) - krl coeff p a x t)))) := by ring
    _ = krC coeff p t x a ω * (Real.exp (-(krl coeff p a x t)) *
        (t * krMd coeff p a x t - krl coeff p a x t * krM coeff p a x t)) := by
        rw [hinner]
    _ = krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t) := by
        rw [hkey]

theorem Ex_sub {p : ℝ} (u w : (κ → Bool) → ℝ) :
    Ex p (fun ω => u ω - w ω) = Ex p u - Ex p w := by
  rw [show (fun ω => u ω - w ω) = fun ω => u ω + (-1) * w ω from
    funext fun ω => by ring]
  rw [Ex_add, Ex_smul]
  ring

/-- Per-coordinate A-term bound: `Ex[g_x log(g_x/E_x g_x)] ≤ ψ·Ex[f·D_{τ,x}]`. -/
theorem A_percoord_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    (hB : ∀ a x, |coeff a x| ≤ 1) {t : ℝ} (ht : 0 ≤ t) (x : κ) :
    Ex p (fun ω => krg coeff p t x ω *
        Real.log (krg coeff p t x ω / condEx p x (krg coeff p t x) ω)) ≤
      ((Real.exp (2 * t) + 1) / 2) *
        Ex p (fun ω => krf coeff p t ω *
          (t * krld coeff p (krTau coeff p t ω) x t -
            krl coeff p (krTau coeff p t ω) x t)) := by
  have step1 : Ex p (fun ω => krg coeff p t x ω *
      Real.log (krg coeff p t x ω / condEx p x (krg coeff p t x) ω)) ≤
      ∑ a : ι, Ex p (fun ω => condEx p x (krInd coeff p t a) ω *
        (Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) *
          (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t)))) := by
    refine le_trans (Ex_mono h0 h1 (krg_xlogx_le h0 h1 coeff t x)) ?_
    rw [Ex_finsum Finset.univ (fun a ω => condEx p x (krInd coeff p t a) ω *
      (Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) *
        (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t))))]
  have step2 : ∀ a : ι,
      Ex p (fun ω => condEx p x (krInd coeff p t a) ω *
        (Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) *
          (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t)))) =
      Ex p (fun ω => krInd coeff p t a ω *
        (krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t))) := by
    intro a
    have hstep : Ex p (fun ω => condEx p x (krInd coeff p t a) ω *
        (Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) *
          (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t)))) =
        Ex p (fun ω => (Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) *
          (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t))) *
            condEx p x (krInd coeff p t a) ω) :=
      Ex_congr fun ω => mul_comm _ _
    rw [hstep]
    rw [Ex_mul_fiberconst h0 h1 x
      (fun ω => Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) *
        (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t)))
      (condEx p x (krInd coeff p t a))
      (fun ω b => condEx_apply_update x _ ω b)]
    have hG : Ex p (fun ω => condEx p x
        (fun ω' => Real.exp (-(t * linSum coeff p a ω' + krL coeff p a t)) *
          (-(t * linSummand coeff p a x (ω' x) + krl coeff p a x t))) ω *
        condEx p x (krInd coeff p t a) ω) =
        Ex p (fun ω => (krC coeff p t x a ω *
          (t * krld coeff p a x t - krl coeff p a x t)) *
          condEx p x (krInd coeff p t a) ω) :=
      Ex_congr fun ω => by rw [condEx_G h0 h1 coeff t x a ω]
    rw [hG]
    have hback : Ex p (fun ω => krInd coeff p t a ω *
        (krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t))) =
        Ex p (fun ω => condEx p x (krInd coeff p t a) ω *
          (krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t))) :=
      Ex_mul_fiberconst h0 h1 x (krInd coeff p t a)
        (fun ω => krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t))
        (fun ω b => by
          show krC coeff p t x a (Function.update ω x b) *
              (t * krld coeff p a x t - krl coeff p a x t) =
            krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t)
          rw [krC_fiberconst])
    rw [hback]
    exact Ex_congr fun ω => by ring
  have step3 : ∑ a : ι, Ex p (fun ω => krInd coeff p t a ω *
      (krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t))) =
      Ex p (fun ω => krf coeff p t ω * Real.exp (krEta coeff p t x ω) *
        (t * krld coeff p (krTau coeff p t ω) x t -
          krl coeff p (krTau coeff p t ω) x t)) := by
    rw [← Ex_finsum Finset.univ (fun a ω => krInd coeff p t a ω *
      (krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t)))]
    refine Ex_congr fun ω => ?_
    rw [sum_krInd_mul coeff p t ω
      (fun a => krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t))]
    rw [← krf_mul_exp_eta coeff p t x ω]
  have step4 : Ex p (fun ω => krf coeff p t ω * Real.exp (krEta coeff p t x ω) *
      (t * krld coeff p (krTau coeff p t ω) x t -
        krl coeff p (krTau coeff p t ω) x t)) ≤
      ((Real.exp (2 * t) + 1) / 2) *
        Ex p (fun ω => krf coeff p t ω *
          (t * krld coeff p (krTau coeff p t ω) x t -
            krl coeff p (krTau coeff p t ω) x t)) := by
    rw [← Ex_smul]
    apply Ex_mono h0 h1
    intro ω
    have hD := krl_tderiv_sub_nonneg h0 h1 coeff (krTau coeff p t ω) x t
    have hψ := exp_krEta_le_psi h0 h1 hB x ht ω
    have hf := (krf_pos coeff p t ω).le
    calc krf coeff p t ω * Real.exp (krEta coeff p t x ω) *
        (t * krld coeff p (krTau coeff p t ω) x t -
          krl coeff p (krTau coeff p t ω) x t) ≤
        krf coeff p t ω * ((Real.exp (2 * t) + 1) / 2) *
        (t * krld coeff p (krTau coeff p t ω) x t -
          krl coeff p (krTau coeff p t ω) x t) := by
          apply mul_le_mul_of_nonneg_right _ hD
          exact mul_le_mul_of_nonneg_left hψ hf
      _ = (Real.exp (2 * t) + 1) / 2 * (krf coeff p t ω *
          (t * krld coeff p (krTau coeff p t ω) x t -
            krl coeff p (krTau coeff p t ω) x t)) := by ring
  calc Ex p (fun ω => krg coeff p t x ω *
      Real.log (krg coeff p t x ω / condEx p x (krg coeff p t x) ω)) ≤
      ∑ a : ι, Ex p (fun ω => condEx p x (krInd coeff p t a) ω *
        (Real.exp (-(t * linSum coeff p a ω + krL coeff p a t)) *
          (-(t * linSummand coeff p a x (ω x) + krl coeff p a x t)))) := step1
    _ = ∑ a : ι, Ex p (fun ω => krInd coeff p t a ω *
        (krC coeff p t x a ω * (t * krld coeff p a x t - krl coeff p a x t))) :=
        Finset.sum_congr rfl fun a _ => step2 a
    _ = Ex p (fun ω => krf coeff p t ω * Real.exp (krEta coeff p t x ω) *
        (t * krld coeff p (krTau coeff p t ω) x t -
          krl coeff p (krTau coeff p t ω) x t)) := step3
    _ ≤ _ := step4

/-- Summed A-term bound (Klein–Rio (4.17)+(4.20)). -/
theorem A_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq)
    {t : ℝ} (ht : 0 < t) :
    ∑ x : κ, Ex p (fun ω => krg coeff p t x ω *
        Real.log (krg coeff p t x ω / condEx p x (krg coeff p t x) ω)) ≤
      ((Real.exp (2 * t) + 1) / 2) * (sigmaSq * (1 + (t - 1) * Real.exp t)) *
        krF coeff p t := by
  have hψ0 : (0:ℝ) ≤ (Real.exp (2 * t) + 1) / 2 := by positivity
  calc ∑ x : κ, Ex p (fun ω => krg coeff p t x ω *
      Real.log (krg coeff p t x ω / condEx p x (krg coeff p t x) ω)) ≤
      ∑ x : κ, ((Real.exp (2 * t) + 1) / 2) *
        Ex p (fun ω => krf coeff p t ω *
          (t * krld coeff p (krTau coeff p t ω) x t -
            krl coeff p (krTau coeff p t ω) x t)) :=
        Finset.sum_le_sum fun x _ => A_percoord_le h0 h1 hB ht.le x
    _ = ((Real.exp (2 * t) + 1) / 2) *
        Ex p (fun ω => ∑ x : κ, krf coeff p t ω *
          (t * krld coeff p (krTau coeff p t ω) x t -
            krl coeff p (krTau coeff p t ω) x t)) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Ex_finsum Finset.univ (fun x ω => krf coeff p t ω *
          (t * krld coeff p (krTau coeff p t ω) x t -
            krl coeff p (krTau coeff p t ω) x t))]
    _ = ((Real.exp (2 * t) + 1) / 2) *
        Ex p (fun ω => krf coeff p t ω *
          (t * krLd coeff p (krTau coeff p t ω) t -
            krL coeff p (krTau coeff p t ω) t)) := by
        congr 1
        refine Ex_congr fun ω => ?_
        rw [← Finset.mul_sum]
        congr 1
        unfold krLd krL
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ ≤ ((Real.exp (2 * t) + 1) / 2) *
        Ex p (fun ω => krf coeff p t ω *
          (sigmaSq * (1 + (t - 1) * Real.exp t))) := by
        apply mul_le_mul_of_nonneg_left _ hψ0
        apply Ex_mono h0 h1
        intro ω
        apply mul_le_mul_of_nonneg_left _ (krf_pos coeff p t ω).le
        exact krL_tderiv_sub_le h0 h1 (fun x => hB (krTau coeff p t ω) x)
          (hVar (krTau coeff p t ω)) ht
    _ = ((Real.exp (2 * t) + 1) / 2) * (sigmaSq * (1 + (t - 1) * Real.exp t)) *
        krF coeff p t := by
        have : Ex p (fun ω => krf coeff p t ω *
            (sigmaSq * (1 + (t - 1) * Real.exp t))) =
            (sigmaSq * (1 + (t - 1) * Real.exp t)) * krF coeff p t := by
          rw [show (fun ω => krf coeff p t ω *
              (sigmaSq * (1 + (t - 1) * Real.exp t))) =
              (fun ω => (sigmaSq * (1 + (t - 1) * Real.exp t)) *
                krf coeff p t ω) from funext fun ω => by ring]
          exact Ex_smul _ _
        rw [this]
        ring

/-! ### Lemma 4.3 (the B-term) and the master inequality -/

/-- `u ↦ e^u − 1 − c·u` is nonincreasing below `log c`. -/
theorem exp_sub_psi_mono {c u v : ℝ} (huv : u ≤ v) (hv : Real.exp v ≤ c) :
    Real.exp v - 1 - c * v ≤ Real.exp u - 1 - c * u := by
  have h2 : Real.exp v * (1 - (v - u)) ≤ Real.exp u := by
    have h := Real.add_one_le_exp (u - v)
    have h3 : Real.exp u = Real.exp v * Real.exp (u - v) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h3]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos v).le
    linarith
  nlinarith [h2, mul_le_mul_of_nonneg_right hv (sub_nonneg.mpr huv)]

/-- Klein–Rio (4.13)–(4.14): `∑_x (Ex g_x − F) ≤ ψ·(S − Ex[f log f])`. -/
theorem sum_Ex_krg_sub_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    (hB : ∀ a x, |coeff a x| ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    ∑ x : κ, (Ex p (krg coeff p t x) - krF coeff p t) ≤
      ((Real.exp (2 * t) + 1) / 2) *
        ((∑ x : κ, Ex p (fun ω => krf coeff p t ω *
          Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω))) -
         Ex p (fun ω => krf coeff p t ω * Real.log (krf coeff p t ω))) := by
  set ψv := (Real.exp (2 * t) + 1) / 2 with hψdef
  -- Pointwise L1 inequality
  have hpoint : ∀ (x : κ) (ω : κ → Bool),
      krf coeff p t ω * Real.exp (krEta coeff p t x ω) - krf coeff p t ω ≤
        (condEx p x (krf coeff p t) ω - krf coeff p t ω +
          ψv * (krf coeff p t ω *
            Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω))) +
        ψv * (krf coeff p t ω * krEta coeff p t x ω) := by
    intro x ω
    have hfpos := krf_pos coeff p t ω
    have hfxpos : 0 < condEx p x (krf coeff p t) ω :=
      condEx_pos h0 h1 x (krf_pos coeff p t) ω
    have hratio : condEx p x (krf coeff p t) ω / krf coeff p t ω ≤
        Real.exp (krEta coeff p t x ω) := by
      rw [div_le_iff₀ hfpos]
      calc condEx p x (krf coeff p t) ω ≤
          krf coeff p t ω * Real.exp (krEta coeff p t x ω) :=
            condEx_krf_le_mul h0 h1 coeff x t ω
        _ = Real.exp (krEta coeff p t x ω) * krf coeff p t ω := by ring
    have hlogle : Real.log (condEx p x (krf coeff p t) ω / krf coeff p t ω) ≤
        krEta coeff p t x ω := by
      have := Real.log_le_log (div_pos hfxpos hfpos) hratio
      rwa [Real.log_exp] at this
    have hexppsi := exp_krEta_le_psi h0 h1 hB x ht ω
    have hmono := exp_sub_psi_mono hlogle hexppsi
    rw [Real.exp_log (div_pos hfxpos hfpos)] at hmono
    -- hmono : e^η − 1 − ψη ≤ f^x/f − 1 − ψ·log(f^x/f)
    have hmul := mul_le_mul_of_nonneg_left hmono hfpos.le
    have hlogflip : Real.log (condEx p x (krf coeff p t) ω / krf coeff p t ω) =
        -Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω) := by
      rw [Real.log_div (ne_of_gt hfxpos) (ne_of_gt hfpos),
        Real.log_div (ne_of_gt hfpos) (ne_of_gt hfxpos)]
      ring
    rw [hlogflip] at hmul
    have hdiv : krf coeff p t ω *
        (condEx p x (krf coeff p t) ω / krf coeff p t ω) =
        condEx p x (krf coeff p t) ω := by
      field_simp
    rw [← hψdef] at hmul
    nlinarith [hmul, hdiv]
  -- Ex both sides, per x
  have hperx : ∀ x : κ, Ex p (krg coeff p t x) - krF coeff p t ≤
      ψv * Ex p (fun ω => krf coeff p t ω *
        Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω)) +
      ψv * Ex p (fun ω => krf coeff p t ω * krEta coeff p t x ω) := by
    intro x
    have hlhs : Ex p (krg coeff p t x) - krF coeff p t =
        Ex p (fun ω => krf coeff p t ω * Real.exp (krEta coeff p t x ω) -
          krf coeff p t ω) := by
      rw [Ex_sub, Ex_krg_eq h0 h1 coeff t x]
      rfl
    have hexcond : Ex p (condEx p x (krf coeff p t)) = krF coeff p t :=
      Ex_condEx h0 h1 x (krf coeff p t)
    have hEmono := Ex_mono h0 h1 (fun ω => hpoint x ω)
    rw [hlhs]
    calc Ex p (fun ω => krf coeff p t ω * Real.exp (krEta coeff p t x ω) -
        krf coeff p t ω) ≤
        Ex p (fun ω => (condEx p x (krf coeff p t) ω - krf coeff p t ω +
          ψv * (krf coeff p t ω *
            Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω))) +
          ψv * (krf coeff p t ω * krEta coeff p t x ω)) := hEmono
      _ = (Ex p (condEx p x (krf coeff p t)) - krF coeff p t) +
          ψv * Ex p (fun ω => krf coeff p t ω *
            Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω)) +
          ψv * Ex p (fun ω => krf coeff p t ω * krEta coeff p t x ω) := by
          rw [Ex_add, Ex_add, Ex_sub, Ex_smul, Ex_smul,
            show krF coeff p t = Ex p (krf coeff p t) from rfl]
      _ = ψv * Ex p (fun ω => krf coeff p t ω *
            Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω)) +
          ψv * Ex p (fun ω => krf coeff p t ω * krEta coeff p t x ω) := by
          rw [hexcond]
          ring
  -- Sum over x; the η-sum telescopes to −Ex[f log f].
  have hsumEta : ∑ x : κ, Ex p (fun ω => krf coeff p t ω * krEta coeff p t x ω) =
      -Ex p (fun ω => krf coeff p t ω * Real.log (krf coeff p t ω)) := by
    rw [← Ex_finsum Finset.univ (fun x ω => krf coeff p t ω * krEta coeff p t x ω)]
    rw [show -Ex p (fun ω => krf coeff p t ω * Real.log (krf coeff p t ω)) =
      Ex p (fun ω => (-1) * (krf coeff p t ω * Real.log (krf coeff p t ω))) from by
        rw [Ex_smul]; ring]
    refine Ex_congr fun ω => ?_
    rw [← Finset.mul_sum, sum_krEta coeff p t ω, log_krf coeff p t ω]
    ring
  calc ∑ x : κ, (Ex p (krg coeff p t x) - krF coeff p t) ≤
      ∑ x : κ, (ψv * Ex p (fun ω => krf coeff p t ω *
        Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω)) +
        ψv * Ex p (fun ω => krf coeff p t ω * krEta coeff p t x ω)) :=
      Finset.sum_le_sum fun x _ => hperx x
    _ = ψv * (∑ x : κ, Ex p (fun ω => krf coeff p t ω *
        Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω))) +
        ψv * (∑ x : κ, Ex p (fun ω => krf coeff p t ω * krEta coeff p t x ω)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by
        rw [hsumEta]
        ring

/-- Klein–Rio (4.15): the B-term against `log ψ · ∑ (Ex g − F)`. -/
theorem B_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    (hB : ∀ a x, |coeff a x| ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    ∑ x : κ, Ex p (fun ω => (krf coeff p t ω - krg coeff p t x ω) *
        Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω)) ≤
      Real.log ((Real.exp (2 * t) + 1) / 2) *
        ∑ x : κ, (Ex p (krg coeff p t x) - krF coeff p t) := by
  have hperx : ∀ x : κ,
      Ex p (fun ω => (krf coeff p t ω - krg coeff p t x ω) *
        Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω)) ≤
      Real.log ((Real.exp (2 * t) + 1) / 2) *
        (Ex p (krg coeff p t x) - krF coeff p t) := by
    intro x
    have hpt : ∀ ω, (krf coeff p t ω - krg coeff p t x ω) *
        Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω) ≤
        Real.log ((Real.exp (2 * t) + 1) / 2) *
          (krg coeff p t x ω - krf coeff p t ω) := by
      intro ω
      have hfpos := krf_pos coeff p t ω
      have hfxpos : 0 < condEx p x (krf coeff p t) ω :=
        condEx_pos h0 h1 x (krf_pos coeff p t) ω
      have hgf : 0 ≤ krg coeff p t x ω - krf coeff p t ω :=
        sub_nonneg.mpr (krf_le_krg h0 h1 coeff t x ω)
      have hratio : condEx p x (krf coeff p t) ω / krf coeff p t ω ≤
          (Real.exp (2 * t) + 1) / 2 := by
        rw [div_le_iff₀ hfpos]
        calc condEx p x (krf coeff p t) ω ≤
            krf coeff p t ω * Real.exp (krEta coeff p t x ω) :=
              condEx_krf_le_mul h0 h1 coeff x t ω
          _ ≤ krf coeff p t ω * ((Real.exp (2 * t) + 1) / 2) :=
              mul_le_mul_of_nonneg_left (exp_krEta_le_psi h0 h1 hB x ht ω)
                hfpos.le
          _ = (Real.exp (2 * t) + 1) / 2 * krf coeff p t ω := by ring
      have hloglog : Real.log (condEx p x (krf coeff p t) ω / krf coeff p t ω) ≤
          Real.log ((Real.exp (2 * t) + 1) / 2) :=
        Real.log_le_log (div_pos hfxpos hfpos) hratio
      have hflip : (krf coeff p t ω - krg coeff p t x ω) *
          Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω) =
          (krg coeff p t x ω - krf coeff p t ω) *
            Real.log (condEx p x (krf coeff p t) ω / krf coeff p t ω) := by
        rw [Real.log_div (ne_of_gt hfpos) (ne_of_gt hfxpos),
          Real.log_div (ne_of_gt hfxpos) (ne_of_gt hfpos)]
        ring
      rw [hflip]
      calc (krg coeff p t x ω - krf coeff p t ω) *
          Real.log (condEx p x (krf coeff p t) ω / krf coeff p t ω) ≤
          (krg coeff p t x ω - krf coeff p t ω) *
            Real.log ((Real.exp (2 * t) + 1) / 2) :=
          mul_le_mul_of_nonneg_left hloglog hgf
        _ = Real.log ((Real.exp (2 * t) + 1) / 2) *
            (krg coeff p t x ω - krf coeff p t ω) := by ring
    calc Ex p (fun ω => (krf coeff p t ω - krg coeff p t x ω) *
        Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω)) ≤
        Ex p (fun ω => Real.log ((Real.exp (2 * t) + 1) / 2) *
          (krg coeff p t x ω - krf coeff p t ω)) := Ex_mono h0 h1 hpt
      _ = Real.log ((Real.exp (2 * t) + 1) / 2) *
          (Ex p (krg coeff p t x) - krF coeff p t) := by
          rw [Ex_smul, Ex_sub]
          rfl
  calc ∑ x : κ, Ex p (fun ω => (krf coeff p t ω - krg coeff p t x ω) *
      Real.log (krf coeff p t ω / condEx p x (krf coeff p t) ω)) ≤
      ∑ x : κ, Real.log ((Real.exp (2 * t) + 1) / 2) *
        (Ex p (krg coeff p t x) - krF coeff p t) :=
      Finset.sum_le_sum fun x _ => hperx x
    _ = _ := by rw [← Finset.mul_sum]

/-- **The master entropy inequality** (Klein–Rio (4.19)+(4.20), F′-free form):
for `0 < t` with `ϕ(t) = ψ(t)·log ψ(t) ≤ 1`,
`Ex[f_t log f_t] − (1−ϕ)·F·log F ≤ ψ·σ²·(1+(t−1)eᵗ)·F`. -/
theorem kr_entropy_master (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {t : ℝ} (ht : 0 < t)
    (hφ : ((Real.exp (2 * t) + 1) / 2) *
      Real.log ((Real.exp (2 * t) + 1) / 2) ≤ 1) :
    Ex (p : ℝ) (fun ω => krf coeff (p : ℝ) t ω *
        Real.log (krf coeff (p : ℝ) t ω)) -
      (1 - ((Real.exp (2 * t) + 1) / 2) *
        Real.log ((Real.exp (2 * t) + 1) / 2)) *
        (krF coeff (p : ℝ) t * Real.log (krF coeff (p : ℝ) t)) ≤
      ((Real.exp (2 * t) + 1) / 2) * (sigmaSq * (1 + (t - 1) * Real.exp t)) *
        krF coeff (p : ℝ) t := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set ψv := (Real.exp (2 * t) + 1) / 2 with hψdef
  have hψ1 : (1:ℝ) ≤ ψv := by
    have : (1:ℝ) ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
    rw [hψdef]
    linarith
  have hlogψ : 0 ≤ Real.log ψv := Real.log_nonneg hψ1
  set E := Ex (p : ℝ) (fun ω => krf coeff (p : ℝ) t ω *
    Real.log (krf coeff (p : ℝ) t ω)) with hE
  set F := krF coeff (p : ℝ) t with hF
  set S := ∑ x : κ, Ex (p : ℝ) (fun ω => krf coeff (p : ℝ) t ω *
    Real.log (krf coeff (p : ℝ) t ω / condEx (p : ℝ) x (krf coeff (p : ℝ) t) ω))
    with hS
  set R := ψv * (sigmaSq * (1 + (t - 1) * Real.exp t)) * F with hR
  -- Ent ≤ S
  have hEnt : E - F * Real.log F ≤ S := by
    have h := entropy_tensor_log p hp (krf coeff (p : ℝ) t)
      (krf_pos coeff (p : ℝ) t)
    have hid : ∀ x : κ, Ex (p : ℝ) (fun ω => krf coeff (p : ℝ) t ω *
        Real.log (krf coeff (p : ℝ) t ω)) -
        Ex (p : ℝ) (fun ω => condEx (p : ℝ) x (krf coeff (p : ℝ) t) ω *
          Real.log (condEx (p : ℝ) x (krf coeff (p : ℝ) t) ω)) =
        Ex (p : ℝ) (fun ω => krf coeff (p : ℝ) t ω *
          Real.log (krf coeff (p : ℝ) t ω /
            condEx (p : ℝ) x (krf coeff (p : ℝ) t) ω)) :=
      fun x => entropy_percoord_identity h0p h1p (krf coeff (p : ℝ) t)
        (krf_pos coeff (p : ℝ) t) x
    calc E - F * Real.log F ≤
        ∑ x : κ, (Ex (p : ℝ) (fun ω => krf coeff (p : ℝ) t ω *
          Real.log (krf coeff (p : ℝ) t ω)) -
          Ex (p : ℝ) (fun ω => condEx (p : ℝ) x (krf coeff (p : ℝ) t) ω *
            Real.log (condEx (p : ℝ) x (krf coeff (p : ℝ) t) ω))) := h
      _ = S := Finset.sum_congr rfl fun x _ => hid x
  -- S ≤ A + B
  have hSAB : S ≤
      (∑ x : κ, Ex (p : ℝ) (fun ω => krg coeff (p : ℝ) t x ω *
        Real.log (krg coeff (p : ℝ) t x ω /
          condEx (p : ℝ) x (krg coeff (p : ℝ) t x) ω))) +
      ∑ x : κ, Ex (p : ℝ) (fun ω =>
        (krf coeff (p : ℝ) t ω - krg coeff (p : ℝ) t x ω) *
        Real.log (krf coeff (p : ℝ) t ω /
          condEx (p : ℝ) x (krf coeff (p : ℝ) t) ω)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ =>
      kr_percoord h0p h1p (krf coeff (p : ℝ) t) (krf_pos coeff (p : ℝ) t) x
        (krg coeff (p : ℝ) t x) (krg_pos h0p h1p coeff t x)
  have hA := A_le h0p h1p hB hVar ht
  have hBB := B_le h0p h1p hB ht.le
  have hL2 := sum_Ex_krg_sub_le h0p h1p hB ht.le
  -- B ≤ ϕ·(S − E)
  have hBphi : ∑ x : κ, Ex (p : ℝ) (fun ω =>
      (krf coeff (p : ℝ) t ω - krg coeff (p : ℝ) t x ω) *
      Real.log (krf coeff (p : ℝ) t ω /
        condEx (p : ℝ) x (krf coeff (p : ℝ) t) ω)) ≤
      (ψv * Real.log ψv) * (S - E) := by
    calc ∑ x : κ, Ex (p : ℝ) (fun ω =>
        (krf coeff (p : ℝ) t ω - krg coeff (p : ℝ) t x ω) *
        Real.log (krf coeff (p : ℝ) t ω /
          condEx (p : ℝ) x (krf coeff (p : ℝ) t) ω)) ≤
        Real.log ψv * ∑ x : κ,
          (Ex (p : ℝ) (krg coeff (p : ℝ) t x) - F) := hBB
      _ ≤ Real.log ψv * (ψv * (S - E)) :=
          mul_le_mul_of_nonneg_left hL2 hlogψ
      _ = (ψv * Real.log ψv) * (S - E) := by ring
  -- combine
  have hcomb : S ≤ R + (ψv * Real.log ψv) * (S - E) := by
    calc S ≤ _ + _ := hSAB
      _ ≤ R + (ψv * Real.log ψv) * (S - E) := add_le_add hA hBphi
  have hfactor : 0 ≤ 1 - ψv * Real.log ψv := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hEnt hfactor, hcomb]

end TalagrandCore
end

/-! ## Component: Bennett -/
section
/-
Bennett's inequality for the lower tail of one branch of the linear process.

Main results:
* `expQuad_mono`   : `u ↦ (eᵘ − u − 1)/u²` is monotone (across `0` as well);
* `bennett_pointwise` : `e^{ty} ≤ 1 + ty + y²(eᵗ − t − 1)` for `t ≥ 0`, `|y| ≤ 1`;
* `krl_le_bennett` / `krL_le_bennett` : per-coordinate and branch cgf bounds;
* `bennett_lower_tail` : the Chernoff lower-tail bound in the weakened
  logarithmic form `exp(−(s/2)·log(1 + s/σ²))`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι]

/-! ### Monotonicity of the Bennett kernel `u ↦ (eᵘ − u − 1)/u²` -/

/-- Derivative of `N'(y) = (y − 1)eʸ + 1`, the derivative of the numerator
`N(y) = (y − 2)eʸ + y + 2` of the kernel derivative. -/
private theorem NQd_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - 1) * Real.exp y + 1) (x * Real.exp x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - 1) * Real.exp y)
      (1 * Real.exp x + (x - 1) * Real.exp x) x :=
    ((hasDerivAt_id x).sub_const 1).mul (Real.hasDerivAt_exp x)
  have h2 := h1.add_const 1
  exact h2.congr_deriv (by ring)

/-- `(s − 1)eˢ + 1 ≥ 0` for all `s` (minimum at `0`). -/
private theorem NQd_nonneg (s : ℝ) : 0 ≤ (s - 1) * Real.exp s + 1 := by
  rcases le_total 0 s with hs | hs
  · have key := nonneg_of_deriv_nonneg_Ici
      (f := fun y : ℝ => (y - 1) * Real.exp y + 1)
      (f' := fun y : ℝ => y * Real.exp y)
      (fun y _ => NQd_hasDerivAt y)
      (by norm_num)
      (fun y hy => by positivity)
      s hs
    linarith
  · have key := nonpos_of_deriv_nonneg_Iic
      (f := fun y : ℝ => -((y - 1) * Real.exp y + 1))
      (f' := fun y : ℝ => -(y * Real.exp y))
      (fun y _ => (NQd_hasDerivAt y).neg)
      (by norm_num)
      (fun y hy => by nlinarith [Real.exp_pos y])
      s hs
    linarith

private theorem NQ_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y + y + 2)
      ((x - 1) * Real.exp x + 1) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - 2) * Real.exp y)
      (1 * Real.exp x + (x - 2) * Real.exp x) x :=
    ((hasDerivAt_id x).sub_const 2).mul (Real.hasDerivAt_exp x)
  have h2 := (h1.add (hasDerivAt_id x)).add_const 2
  exact h2.congr_deriv (by ring)

/-- `N(s) = (s − 2)eˢ + s + 2 ≥ 0` for `s ≥ 0`. -/
private theorem NQ_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ (s - 2) * Real.exp s + s + 2 := by
  have key := nonneg_of_deriv_nonneg_Ici
    (f := fun y : ℝ => (y - 2) * Real.exp y + y + 2)
    (f' := fun y : ℝ => (y - 1) * Real.exp y + 1)
    (fun y _ => NQ_hasDerivAt y)
    (by norm_num)
    (fun y _ => NQd_nonneg y)
    s hs
  linarith

/-- `N(s) = (s − 2)eˢ + s + 2 ≤ 0` for `s ≤ 0`. -/
private theorem NQ_nonpos {s : ℝ} (hs : s ≤ 0) :
    (s - 2) * Real.exp s + s + 2 ≤ 0 := by
  have key := nonpos_of_deriv_nonneg_Iic
    (f := fun y : ℝ => (y - 2) * Real.exp y + y + 2)
    (f' := fun y : ℝ => (y - 1) * Real.exp y + 1)
    (fun y _ => NQ_hasDerivAt y)
    (by norm_num)
    (fun y _ => NQd_nonneg y)
    s hs
  linarith

/-- Derivative of the Bennett kernel at `x ≠ 0`. -/
private theorem hQ_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun s : ℝ => (Real.exp s - s - 1) / s ^ 2)
      (((x - 2) * Real.exp x + x + 2) / x ^ 3) x := by
  have hnum : HasDerivAt (fun s : ℝ => Real.exp s - s - 1) (Real.exp x - 1) x := by
    simpa using ((Real.hasDerivAt_exp x).sub (hasDerivAt_id x)).sub_const 1
  have hden : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hd2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hdiv := hnum.div hden hd2
  have h3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx
  have h4 : (x ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hd2
  refine hdiv.congr_deriv ?_
  rw [div_eq_div_iff h4 h3]
  ring

private theorem hQ_mono_Ioi :
    MonotoneOn (fun s : ℝ => (Real.exp s - s - 1) / s ^ 2) (Set.Ioi (0:ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx
    exact (hQ_hasDerivAt (ne_of_gt (Set.mem_Ioi.mp hx))).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact ((hQ_hasDerivAt (ne_of_gt (Set.mem_Ioi.mp hx))).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : (0:ℝ) < x := Set.mem_Ioi.mp hx
    rw [(hQ_hasDerivAt (ne_of_gt hx0)).deriv]
    have h3 : (0:ℝ) < x ^ 3 := by positivity
    exact div_nonneg (NQ_nonneg hx0.le) h3.le

private theorem hQ_mono_Iio :
    MonotoneOn (fun s : ℝ => (Real.exp s - s - 1) / s ^ 2) (Set.Iio (0:ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iio 0)
  · intro x hx
    exact (hQ_hasDerivAt (ne_of_lt (Set.mem_Iio.mp hx))).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iio] at hx
    exact ((hQ_hasDerivAt (ne_of_lt (Set.mem_Iio.mp hx))).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Iio] at hx
    have hx0 : x < (0:ℝ) := Set.mem_Iio.mp hx
    rw [(hQ_hasDerivAt (ne_of_lt hx0)).deriv]
    rw [div_nonneg_iff]
    right
    refine ⟨NQ_nonpos hx0.le, ?_⟩
    nlinarith [sq_nonneg x]

/-- `eᵘ − u − 1 ≤ u²/2` for `u ≤ 0`. -/
private theorem exp_sub_le_half_sq {u : ℝ} (hu : u ≤ 0) :
    Real.exp u - u - 1 ≤ u ^ 2 / 2 := by
  have hmain := nonpos_of_deriv_nonneg_Iic
    (f := fun s : ℝ => (Real.exp s - s - 1) - s ^ 2 / 2)
    (f' := fun s : ℝ => Real.exp s - 1 - s)
    (fun s _hs => by
      have h1 : HasDerivAt (fun s : ℝ => Real.exp s - s - 1) (Real.exp s - 1) s := by
        simpa using ((Real.hasDerivAt_exp s).sub (hasDerivAt_id s)).sub_const 1
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s := by
        have := (hasDerivAt_pow 2 s).div_const 2
        exact this.congr_deriv (by ring)
      exact h1.sub h2)
    (by norm_num)
    (fun s _hs => by linarith [Real.add_one_le_exp s])
    u hu
  linarith [hmain]

/-- `v²/2 ≤ eᵛ − v − 1` for `v ≥ 0`. -/
private theorem half_sq_le_exp_sub {v : ℝ} (hv : 0 ≤ v) :
    v ^ 2 / 2 ≤ Real.exp v - v - 1 := by
  have hmain := nonneg_of_deriv_nonneg_Ici
    (f := fun s : ℝ => (Real.exp s - s - 1) - s ^ 2 / 2)
    (f' := fun s : ℝ => Real.exp s - 1 - s)
    (fun s _hs => by
      have h1 : HasDerivAt (fun s : ℝ => Real.exp s - s - 1) (Real.exp s - 1) s := by
        simpa using ((Real.hasDerivAt_exp s).sub (hasDerivAt_id s)).sub_const 1
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s := by
        have := (hasDerivAt_pow 2 s).div_const 2
        exact this.congr_deriv (by ring)
      exact h1.sub h2)
    (by norm_num)
    (fun s _hs => by linarith [Real.add_one_le_exp s])
    v hv
  linarith [hmain]

/-- Monotonicity of the Bennett kernel ratio `u ↦ (eᵘ − u − 1)/u²`. -/
theorem expQuad_mono {u v : ℝ} (huv : u ≤ v) (hu : u ≠ 0) (hv : v ≠ 0) :
    (Real.exp u - u - 1) / u ^ 2 ≤ (Real.exp v - v - 1) / v ^ 2 := by
  rcases lt_or_ge 0 u with hu0 | hu0
  · exact hQ_mono_Ioi (Set.mem_Ioi.mpr hu0)
      (Set.mem_Ioi.mpr (lt_of_lt_of_le hu0 huv)) huv
  · have hu0' : u < 0 := lt_of_le_of_ne hu0 hu
    rcases lt_or_ge v 0 with hv0 | hv0
    · exact hQ_mono_Iio (Set.mem_Iio.mpr hu0') (Set.mem_Iio.mpr hv0) huv
    · have hv0' : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hv)
      have hu2 : (0:ℝ) < u ^ 2 := (sq_nonneg u).lt_of_ne (Ne.symm (pow_ne_zero 2 hu))
      have hv2 : (0:ℝ) < v ^ 2 := (sq_nonneg v).lt_of_ne (Ne.symm (pow_ne_zero 2 hv))
      have h1 : (Real.exp u - u - 1) / u ^ 2 ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hu2 (by norm_num : (0:ℝ) < 2)]
        have := exp_sub_le_half_sq hu0'.le
        linarith
      have h2 : (1:ℝ) / 2 ≤ (Real.exp v - v - 1) / v ^ 2 := by
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hv2]
        have := half_sq_le_exp_sub hv0'.le
        linarith
      linarith

/-! ### The pointwise Bennett kernel bound -/

/-- Pointwise Bennett kernel bound: `e^{ty} ≤ 1 + ty + y²(eᵗ − t − 1)`
for `t ≥ 0` and `−1 ≤ y ≤ 1`. -/
theorem bennett_pointwise {t y : ℝ} (ht : 0 ≤ t) (hy : y ≤ 1) (hy' : -1 ≤ y) :
    Real.exp (t * y) ≤ 1 + t * y + y ^ 2 * (Real.exp t - t - 1) := by
  rcases eq_or_lt_of_le ht with h | ht0
  · rw [← h]
    norm_num
  rcases eq_or_ne y 0 with hy0 | hy0
  · rw [hy0]
    norm_num
  have hty : t * y ≠ 0 := mul_ne_zero (ne_of_gt ht0) hy0
  have hle : t * y ≤ t := by nlinarith
  have hmono := expQuad_mono hle hty (ne_of_gt ht0)
  have hty2 : (0:ℝ) < (t * y) ^ 2 :=
    (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hty))
  have ht2 : (0:ℝ) < t ^ 2 := by positivity
  rw [div_le_div_iff₀ hty2 ht2] at hmono
  -- hmono : (exp (t*y) - t*y - 1) * t^2 ≤ (exp t - t - 1) * (t*y)^2
  have key : Real.exp (t * y) - t * y - 1 ≤ (Real.exp t - t - 1) * y ^ 2 := by
    have h2 : (Real.exp (t * y) - t * y - 1) * t ^ 2 ≤
        ((Real.exp t - t - 1) * y ^ 2) * t ^ 2 := by linarith [hmono]
    exact le_of_mul_le_mul_right h2 ht2
  linarith [key]

/-! ### Per-coordinate and branch cgf bounds -/

/-- Per-coordinate Bennett bound on the cgf. -/
theorem krl_le_bennett {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    {a : ι} {x : κ} (hB : |coeff a x| ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    krl coeff p a x t ≤ p * (1 - p) * coeff a x ^ 2 * (Real.exp t - t - 1) := by
  have hM := krM_pos h0 h1 coeff a x t
  -- Each branch obeys the pointwise Bennett bound with `y = −linSummand`.
  have hbranch : ∀ b : Bool,
      Real.exp (-(t * linSummand coeff p a x b)) ≤
        1 + t * (-linSummand coeff p a x b) +
          linSummand coeff p a x b ^ 2 * (Real.exp t - t - 1) := by
    intro b
    have habs := abs_le.mp (linSummand_abs_le h0 h1 hB b)
    have hb := bennett_pointwise ht
      (by linarith [habs.1] : -linSummand coeff p a x b ≤ 1)
      (by linarith [habs.2] : -1 ≤ -linSummand coeff p a x b)
    have harg : -(t * linSummand coeff p a x b) =
        t * (-linSummand coeff p a x b) := by ring
    rw [harg]
    calc Real.exp (t * (-linSummand coeff p a x b)) ≤
        1 + t * (-linSummand coeff p a x b) +
          (-linSummand coeff p a x b) ^ 2 * (Real.exp t - t - 1) := hb
      _ = 1 + t * (-linSummand coeff p a x b) +
          linSummand coeff p a x b ^ 2 * (Real.exp t - t - 1) := by ring
  have hbt := bw_nonneg h0 h1 true
  have hbf := bw_nonneg h0 h1 false
  have hsum := bw_sum p
  have havg := linSummand_avg coeff p a x
  have hsq := linSummand_sq_avg coeff p a x
  have m1 := mul_le_mul_of_nonneg_left (hbranch true) hbt
  have m2 := mul_le_mul_of_nonneg_left (hbranch false) hbf
  have hzero : t * (bw p true * linSummand coeff p a x true +
      bw p false * linSummand coeff p a x false) = 0 := by rw [havg]; ring
  have hkey : (bw p true * linSummand coeff p a x true ^ 2 +
      bw p false * linSummand coeff p a x false ^ 2) * (Real.exp t - t - 1) =
      p * (1 - p) * coeff a x ^ 2 * (Real.exp t - t - 1) := by rw [hsq]
  have hMle : krM coeff p a x t ≤
      1 + p * (1 - p) * coeff a x ^ 2 * (Real.exp t - t - 1) := by
    unfold krM
    linarith [m1, m2, hzero, hkey, hsum]
  have hlog := Real.log_le_sub_one_of_pos hM
  calc krl coeff p a x t = Real.log (krM coeff p a x t) := rfl
    _ ≤ krM coeff p a x t - 1 := hlog
    _ ≤ p * (1 - p) * coeff a x ^ 2 * (Real.exp t - t - 1) := by linarith [hMle]

/-- Branch cgf Bennett bound against a variance proxy. -/
theorem krL_le_bennett {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    {a : ι} (hB : ∀ x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq) {t : ℝ} (ht : 0 ≤ t) :
    krL coeff p a t ≤ sigmaSq * (Real.exp t - t - 1) := by
  have hfac : 0 ≤ Real.exp t - t - 1 := by linarith [Real.add_one_le_exp t]
  unfold krL
  calc ∑ x : κ, krl coeff p a x t
      ≤ ∑ x : κ, p * (1 - p) * coeff a x ^ 2 * (Real.exp t - t - 1) :=
        Finset.sum_le_sum fun x _ => krl_le_bennett h0 h1 (hB x) ht
    _ = (∑ x : κ, p * (1 - p) * coeff a x ^ 2) * (Real.exp t - t - 1) := by
        rw [Finset.sum_mul]
    _ ≤ sigmaSq * (Real.exp t - t - 1) :=
        mul_le_mul_of_nonneg_right hVar hfac

/-! ### The Chernoff lower tail (log form) -/

/-- Bennett lower-tail bound for one branch of the linear process, in the
weakened logarithmic form. -/
theorem bennett_lower_tail {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    {a : ι} (hB : ∀ x, |coeff a x| ≤ 1) {sigmaSq : ℝ} (hs : 0 < sigmaSq)
    (hVar : ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq) {s : ℝ} (hs0 : 0 ≤ s) :
    Ex p (fun ω => if linSum coeff p a ω ≤ -s then (1:ℝ) else 0) ≤
      Real.exp (-((s / 2) * Real.log (1 + s / sigmaSq))) := by
  set t := Real.log (1 + s / sigmaSq) with htdef
  have hsdiv : 0 ≤ s / sigmaSq := div_nonneg hs0 hs.le
  have hpos1 : (0:ℝ) < 1 + s / sigmaSq := by linarith
  have ht0 : 0 ≤ t := by rw [htdef]; exact Real.log_nonneg (by linarith)
  have hexp_t : Real.exp t = 1 + s / sigmaSq := by
    rw [htdef]; exact Real.exp_log hpos1
  -- Pointwise Chernoff bound for the indicator.
  have hpt : ∀ ω : κ → Bool, (if linSum coeff p a ω ≤ -s then (1:ℝ) else 0) ≤
      Real.exp (-(t * s)) * Real.exp (-(t * linSum coeff p a ω)) := by
    intro ω
    by_cases hcase : linSum coeff p a ω ≤ -s
    · rw [if_pos hcase, ← Real.exp_add]
      have hprod : t * linSum coeff p a ω ≤ t * (-s) :=
        mul_le_mul_of_nonneg_left hcase ht0
      have hge : (0:ℝ) ≤ -(t * s) + -(t * linSum coeff p a ω) := by
        nlinarith [hprod]
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (-(t * s) + -(t * linSum coeff p a ω)) :=
            Real.exp_le_exp.mpr hge
    · rw [if_neg hcase]
      positivity
  have hExPos : 0 < Ex p (fun ω => Real.exp (-(t * linSum coeff p a ω))) :=
    Ex_pos h0 h1 fun ω => Real.exp_pos _
  have hkrL := krL_le_bennett h0 h1 hB hVar ht0
  have hcomb : Ex p (fun ω => if linSum coeff p a ω ≤ -s then (1:ℝ) else 0) ≤
      Real.exp (-(t * s) + sigmaSq * (Real.exp t - t - 1)) := by
    calc Ex p (fun ω => if linSum coeff p a ω ≤ -s then (1:ℝ) else 0)
        ≤ Ex p (fun ω => Real.exp (-(t * s)) *
            Real.exp (-(t * linSum coeff p a ω))) := Ex_mono h0 h1 hpt
      _ = Real.exp (-(t * s)) *
            Ex p (fun ω => Real.exp (-(t * linSum coeff p a ω))) := Ex_smul _ _
      _ = Real.exp (-(t * s)) * Real.exp (krL coeff p a t) := by
          rw [← log_Ex_exp_neg_linSum h0 h1 coeff a t, Real.exp_log hExPos]
      _ = Real.exp (-(t * s) + krL coeff p a t) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(t * s) + sigmaSq * (Real.exp t - t - 1)) :=
          Real.exp_le_exp.mpr (by linarith [hkrL])
  refine hcomb.trans (Real.exp_le_exp.mpr ?_)
  -- Goal: −ts + σ²(eᵗ − t − 1) ≤ −(s/2)·t  with  t = log(1 + s/σ²).
  rw [hexp_t]
  have hben := hBen_ge_half_mul_log (s / sigmaSq) hsdiv
  unfold hBen at hben
  rw [← htdef] at hben
  have hσ : sigmaSq ≠ 0 := ne_of_gt hs
  have hben2 := mul_le_mul_of_nonneg_left hben hs.le
  have eL : sigmaSq * (s / sigmaSq / 2 * t) = s / 2 * t := by
    field_simp
  have eR : sigmaSq * ((1 + s / sigmaSq) * t - s / sigmaSq) =
      (sigmaSq + s) * t - s := by
    field_simp
  rw [eL, eR] at hben2
  have e3 : sigmaSq * (1 + s / sigmaSq - t - 1) = s - sigmaSq * t := by
    field_simp
    ring
  rw [e3]
  linarith [hben2]

end TalagrandCore
end

/-! ## Component: KRDini -/
section
/-
Klein–Rio machinery, part 5: integrating the differential inequality on
`(0, 1/4]` via the frozen-branch comparison and Mathlib's right-slope fencing
lemma (`image_le_of_liminf_slope_right_le_deriv_boundary`) — no a.e.
derivatives of `F` needed.

Main result `kr_lower_cgf`: for `0 < t ≤ 1/4`,

  log Ex e^{−tZ} ≤ −t·EZ + 4·(σ² + EZ)·t².
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-! ### Numeric kernel bounds on `[0, 1/4]` -/

/-- `e^t ≤ 2` for `t ≤ 1/2`. -/
theorem exp_le_two {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 1/2) : Real.exp t ≤ 2 := by
  calc Real.exp t ≤ Real.exp (1/2) := Real.exp_le_exp.mpr h2
    _ ≤ 1 / (1 - 1/2) := exp_le_one_div_one_sub (by norm_num) (by norm_num)
    _ = 2 := by norm_num

/-- `1 + (t−1)eᵗ ≤ t²` on `[0, 1/4]`. -/
theorem one_add_mul_exp_le_sq {t : ℝ} (h0 : 0 ≤ t) (h4 : t ≤ 1/4) :
    1 + (t - 1) * Real.exp t ≤ t ^ 2 := by
  have hmain := nonneg_of_deriv_nonneg_Icc (a := 0) (b := (1/4 : ℝ))
    (f := fun s => s ^ 2 - (1 + (s - 1) * Real.exp s))
    (f' := fun s => 2 * s - s * Real.exp s)
    (fun s _hs => by
      have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      have h2 : HasDerivAt (fun s : ℝ => 1 + (s - 1) * Real.exp s)
          (Real.exp s + (s - 1) * Real.exp s) s := by
        have hh : HasDerivAt (fun s : ℝ => (s - 1) * Real.exp s)
            (1 * Real.exp s + (s - 1) * Real.exp s) s :=
          ((hasDerivAt_id s).sub_const 1).mul (Real.hasDerivAt_exp s)
        have := hh.const_add 1
        exact this.congr_deriv (by ring)
      have := h1.sub h2
      exact this.congr_deriv (by ring))
    (by norm_num)
    (fun s hs => by
      have hse : Real.exp s ≤ 2 := exp_le_two hs.1.le (by linarith [hs.2])
      have : s * Real.exp s ≤ s * 2 :=
        mul_le_mul_of_nonneg_left hse hs.1.le
      linarith)
  have := hmain t ⟨h0, h4⟩
  linarith

/-- `eᵗ − t − 1 ≤ t²` on `[0, 1/4]`. -/
theorem exp_sub_le_sq {t : ℝ} (h0 : 0 ≤ t) (h4 : t ≤ 1/4) :
    Real.exp t - t - 1 ≤ t ^ 2 := by
  have hmain := nonneg_of_deriv_nonneg_Icc (a := 0) (b := (1/4 : ℝ))
    (f := fun s => s ^ 2 - (Real.exp s - s - 1))
    (f' := fun s => 2 * s + 1 - Real.exp s)
    (fun s _hs => by
      have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
        simpa using hasDerivAt_pow 2 s
      have h2 : HasDerivAt (fun s : ℝ => Real.exp s - s - 1)
          (Real.exp s - 1) s := by
        simpa using ((Real.hasDerivAt_exp s).sub (hasDerivAt_id s)).sub_const 1
      have := h1.sub h2
      exact this.congr_deriv (by ring))
    (by norm_num)
    (fun s hs => by
      have h1' : Real.exp s ≤ 1 / (1 - s) :=
        exp_le_one_div_one_sub hs.1.le (by linarith [hs.2])
      have hpos : 0 < 1 - s := by linarith [hs.2]
      have h2' : 1 / (1 - s) ≤ 2 * s + 1 := by
        rw [div_le_iff₀ hpos]
        nlinarith [hs.1, hs.2]
      show 0 ≤ 2 * s + 1 - Real.exp s
      linarith)
  have := hmain t ⟨h0, h4⟩
  linarith

/-- `ϕ(t) = ψ(t)·log ψ(t) ≤ 2t` on `[0, 1/4]`. -/
theorem phi_le_two_mul {t : ℝ} (h0 : 0 ≤ t) (h4 : t ≤ 1/4) :
    ((Real.exp (2 * t) + 1) / 2) * Real.log ((Real.exp (2 * t) + 1) / 2) ≤
      2 * t := by
  have hup := lemma45_upper t h0 (by linarith)
  have hphi : phiKR t =
      ((Real.exp (2 * t) + 1) / 2) * Real.log ((Real.exp (2 * t) + 1) / 2) := by
    rw [phiKR, psiKR]
  rw [← hphi]
  have he : Real.exp (2 * t) ≤ 2 := exp_le_two (by linarith) (by linarith)
  have hsq : 0 ≤ t ^ 2 / 2 := by positivity
  calc phiKR t ≤ t * Real.exp (2 * t) - t ^ 2 / 2 := hup
    _ ≤ t * 2 - 0 := by
        have := mul_le_mul_of_nonneg_left he h0
        linarith
    _ = 2 * t := by ring

/-- `0 ≤ ϕ(t)` for `t ≥ 0`. -/
theorem phi_nonneg' {t : ℝ} (h0 : 0 ≤ t) :
    0 ≤ ((Real.exp (2 * t) + 1) / 2) * Real.log ((Real.exp (2 * t) + 1) / 2) := by
  have h1 : (1:ℝ) ≤ (Real.exp (2 * t) + 1) / 2 := by
    have : (1:ℝ) ≤ Real.exp (2 * t) := Real.one_le_exp (by linarith)
    linarith
  exact mul_nonneg (by linarith) (Real.log_nonneg h1)

/-! ### Expectation lemmas -/

/-- Jensen for `exp` in sum-land. -/
theorem exp_Ex_le_Ex_exp {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (f : (κ → Bool) → ℝ) :
    Real.exp (Ex p f) ≤ Ex p (fun ω => Real.exp (f ω)) := by
  set m := Ex p f with hm
  have hpt : ∀ ω, Real.exp m + Real.exp m * (f ω - m) ≤ Real.exp (f ω) := by
    intro ω
    have h := Real.add_one_le_exp (f ω - m)
    have h2 : Real.exp (f ω) = Real.exp m * Real.exp (f ω - m) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [Real.exp_pos m, mul_le_mul_of_nonneg_left h (Real.exp_pos m).le]
  have hEx := Ex_mono h0 h1 hpt
  have hlhs : Ex p (fun ω => Real.exp m + Real.exp m * (f ω - m)) =
      Real.exp m := by
    rw [show (fun ω => Real.exp m + Real.exp m * (f ω - m)) =
        (fun ω => (Real.exp m - Real.exp m * m) + Real.exp m * f ω) from
        funext fun ω => by ring]
    rw [Ex_add, Ex_const h0 h1, Ex_smul, ← hm]
    ring
  linarith [hlhs ▸ hEx]

/-- Expectation of a single-coordinate function. -/
theorem Ex_single_coord {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (u : Bool → ℝ)
    (x : κ) :
    Ex p (fun ω => u (ω x)) = bw p true * u true + bw p false * u false := by
  rw [← Ex_condEx h0 h1 x (fun ω => u (ω x))]
  have hconst : ∀ ω, condEx p x (fun ω' => u (ω' x)) ω =
      bw p true * u true + bw p false * u false := by
    intro ω
    show bw p true * u ((Function.update ω x true) x) +
        bw p false * u ((Function.update ω x false) x) = _
    rw [Function.update_self, Function.update_self]
  rw [Ex_congr hconst, Ex_const h0 h1]

theorem Ex_linSum_eq_zero {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (coeff : ι → κ → ℝ) (a : ι) : Ex p (linSum coeff p a) = 0 := by
  have : Ex p (linSum coeff p a) =
      ∑ x : κ, Ex p (fun ω => linSummand coeff p a x (ω x)) := by
    unfold linSum
    exact Ex_finsum Finset.univ (fun x ω => linSummand coeff p a x (ω x))
  rw [this]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Ex_single_coord h0 h1 (linSummand coeff p a x) x]
  exact linSummand_avg coeff p a x

theorem Ex_Zproc_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (coeff : ι → κ → ℝ) : 0 ≤ Ex p (Zproc coeff p) := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty ι)
  have hpt : ∀ ω, linSum coeff p a₀ ω ≤ Zproc coeff p ω := fun ω =>
    le_supProc (linSummand coeff p) ω a₀
  have := Ex_mono h0 h1 hpt
  rw [Ex_linSum_eq_zero h0 h1 coeff a₀] at this
  exact this

/-- `0 ≤ sigmaSq` comes for free from the variance hypothesis. -/
theorem sigmaSq_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    {coeff : ι → κ → ℝ} {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq) :
    0 ≤ sigmaSq := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty ι)
  refine le_trans ?_ (hVar a₀)
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg _)

/-! ### Continuity of `krF` -/

theorem continuous_krL {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (a : ι) : Continuous (krL coeff p a) :=
  continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_krL h0 h1 coeff a s).continuousAt

theorem continuous_krF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ) :
    Continuous (fun s : ℝ => krF coeff p s) := by
  unfold krF Ex
  apply continuous_finset_sum
  intro ω _
  apply Continuous.mul continuous_const
  show Continuous fun s : ℝ => krf coeff p s ω
  unfold krf krComp
  apply Real.continuous_exp.comp
  apply Continuous.neg
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun a _ =>
    (continuous_id.mul continuous_const).add (continuous_krL h0 h1 coeff a)

/-! ### The Λ lower bound -/

/-- `max_a L_a(t) ≤ σ²·t²` on `[0, 1/4]`. -/
theorem Lmax_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq)
    {t : ℝ} (ht : 0 ≤ t) (ht4 : t ≤ 1/4) :
    Finset.univ.sup' Finset.univ_nonempty (fun a : ι => krL coeff p a t) ≤
      sigmaSq * t ^ 2 := by
  apply Finset.sup'_le
  intro a _
  calc krL coeff p a t ≤ sigmaSq * (Real.exp t - t - 1) :=
      krL_le_bennett h0 h1 (fun x => hB a x) (hVar a) ht
    _ ≤ sigmaSq * t ^ 2 :=
      mul_le_mul_of_nonneg_left (exp_sub_le_sq ht ht4)
        (sigmaSq_nonneg h0 h1 hVar)

/-- `−Λ(t) ≤ t·EZ + σ²·t²` on `[0, 1/4]`. -/
theorem neg_log_krF_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {coeff : ι → κ → ℝ}
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, p * (1 - p) * coeff a x ^ 2 ≤ sigmaSq)
    {t : ℝ} (ht : 0 ≤ t) (ht4 : t ≤ 1/4) :
    -Real.log (krF coeff p t) ≤
      t * Ex p (Zproc coeff p) + sigmaSq * t ^ 2 := by
  set Lmax := Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => krL coeff p a t) with hLmaxdef
  have hJ : Real.exp (-(t * Ex p (Zproc coeff p))) ≤
      Ex p (fun ω => Real.exp (-(t * Zproc coeff p ω))) := by
    have hj := exp_Ex_le_Ex_exp h0 h1 (fun ω => -(t * Zproc coeff p ω))
    have hEx : Ex p (fun ω => -(t * Zproc coeff p ω)) =
        -(t * Ex p (Zproc coeff p)) := by
      rw [show (fun ω => -(t * Zproc coeff p ω)) =
          (fun ω => (-t) * Zproc coeff p ω) from funext fun ω => by ring]
      rw [Ex_smul]
      ring
    rwa [hEx] at hj
  have htr := Ex_exp_neg_tZ_le h0 h1 coeff ht
  have hFpos := krF_pos h0 h1 coeff t
  have hcomb : Real.exp (-(t * Ex p (Zproc coeff p))) ≤
      krF coeff p t * Real.exp Lmax := le_trans hJ htr
  have hlog := Real.log_le_log (Real.exp_pos _) hcomb
  rw [Real.log_exp, Real.log_mul (ne_of_gt hFpos) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  have hLb : Lmax ≤ sigmaSq * t ^ 2 := Lmax_le h0 h1 hB hVar ht ht4
  linarith

/-! ### The frozen-comparison derivative bound -/

theorem krFrozen_pos {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (coeff : ι → κ → ℝ)
    (t s : ℝ) : 0 < krFrozen coeff p t s :=
  Ex_pos h0 h1 fun ω => Real.exp_pos _

/-- At each `0 < x ≤ 1/4`, the frozen comparison `s ↦ log(krFrozen x s)/s` has
a derivative at `x` bounded by `3(σ² + EZ)`. -/
theorem frozen_deriv_bound (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {x : ℝ} (hx : 0 < x) (hx4 : x ≤ 1/4) :
    ∃ D : ℝ,
      HasDerivAt (fun s => Real.log (krFrozen coeff (p : ℝ) x s) / s) D x ∧
      D ≤ 3 * (sigmaSq + Ex (p : ℝ) (Zproc coeff (p : ℝ))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hFpos := krF_pos h0p h1p coeff x
  have hfrozen_self := krFrozen_self coeff (p : ℝ) x
  have hfx_ne : krFrozen coeff (p : ℝ) x x ≠ 0 := by
    rw [hfrozen_self]; exact ne_of_gt hFpos
  have hD := hasDerivAt_krFrozen h0p h1p coeff x
  have hlogD := hD.log hfx_ne
  have hdivD := hlogD.div (hasDerivAt_id x) (ne_of_gt hx)
  refine ⟨_, hdivD, ?_⟩
  -- Now bound the derivative value.
  have hφle : ((Real.exp (2 * x) + 1) / 2) *
      Real.log ((Real.exp (2 * x) + 1) / 2) ≤ 2 * x := phi_le_two_mul hx.le hx4
  have hφ0 : 0 ≤ ((Real.exp (2 * x) + 1) / 2) *
      Real.log ((Real.exp (2 * x) + 1) / 2) := phi_nonneg' hx.le
  have hφ1 : ((Real.exp (2 * x) + 1) / 2) *
      Real.log ((Real.exp (2 * x) + 1) / 2) ≤ 1 := by linarith
  have hmaster := kr_entropy_master p hp coeff hB hVar hx hφ1
  have hDle := krFrozenD_mul_le h0p h1p coeff hx.le
  have hψle : (Real.exp (2 * x) + 1) / 2 ≤ 3 / 2 := by
    have := exp_le_two (t := 2 * x) (by linarith) (by linarith)
    linarith
  have hs0 : 0 ≤ sigmaSq := sigmaSq_nonneg h0p h1p hVar
  have hEZ0 : 0 ≤ Ex (p : ℝ) (Zproc coeff (p : ℝ)) := Ex_Zproc_nonneg h0p h1p coeff
  have hVb : sigmaSq * (1 + (x - 1) * Real.exp x) ≤ sigmaSq * x ^ 2 :=
    mul_le_mul_of_nonneg_left (one_add_mul_exp_le_sq hx.le hx4) hs0
  have hVb0 : 0 ≤ sigmaSq * (1 + (x - 1) * Real.exp x) :=
    mul_nonneg hs0 (one_add_mul_exp_nonneg hx.le)
  have hψV : ((Real.exp (2 * x) + 1) / 2) *
      (sigmaSq * (1 + (x - 1) * Real.exp x)) ≤ (3/2) * (sigmaSq * x ^ 2) := by
    calc ((Real.exp (2 * x) + 1) / 2) * (sigmaSq * (1 + (x - 1) * Real.exp x)) ≤
        (3/2) * (sigmaSq * (1 + (x - 1) * Real.exp x)) :=
          mul_le_mul_of_nonneg_right hψle hVb0
      _ ≤ (3/2) * (sigmaSq * x ^ 2) := by linarith [hVb]
  have hnegΛ := neg_log_krF_le h0p h1p hB hVar hx.le hx4
  -- Fold the abbreviations everywhere.
  set EZ := Ex (p : ℝ) (Zproc coeff (p : ℝ)) with hEZdef
  set F := krF coeff (p : ℝ) x with hFdef
  set E := Ex (p : ℝ) (fun ω => krf coeff (p : ℝ) x ω *
    Real.log (krf coeff (p : ℝ) x ω)) with hEdef
  set φv := ((Real.exp (2 * x) + 1) / 2) *
    Real.log ((Real.exp (2 * x) + 1) / 2) with hφdef
  set ψv := (Real.exp (2 * x) + 1) / 2 with hψdef
  set Vb := sigmaSq * (1 + (x - 1) * Real.exp x) with hVbdef
  have hfs : krFrozen coeff (p : ℝ) x x = F := krFrozen_self coeff (p : ℝ) x
  have hx2 : (0:ℝ) < x ^ 2 := by positivity
  rw [hfs, mul_one]
  simp only [id_eq]
  rw [div_le_iff₀ hx2]
  -- key inequality chain
  have hk1 : krFrozenD coeff (p : ℝ) x / F * x ≤ E / F := by
    rw [show krFrozenD coeff (p : ℝ) x / F * x =
      x * krFrozenD coeff (p : ℝ) x / F from by ring]
    exact (div_le_div_iff_of_pos_right hFpos).mpr hDle
  have hEb : E ≤ (1 - φv) * (F * Real.log F) + ψv * Vb * F := by linarith [hmaster]
  have hk2 : E / F ≤ (1 - φv) * Real.log F + ψv * Vb := by
    have h := (div_le_div_iff_of_pos_right hFpos).mpr hEb
    have hident : ((1 - φv) * (F * Real.log F) + ψv * Vb * F) / F =
        (1 - φv) * Real.log F + ψv * Vb := by
      field_simp
    linarith [hident ▸ h]
  have hφlog : φv * (-Real.log F) ≤ φv * (x * EZ + sigmaSq * x ^ 2) :=
    mul_le_mul_of_nonneg_left hnegΛ hφ0
  have hφx : φv * (x * EZ + sigmaSq * x ^ 2) ≤
      2 * x * (x * EZ + sigmaSq * x ^ 2) := by
    apply mul_le_mul_of_nonneg_right hφle
    positivity
  have hpoly : 2 * x * (x * EZ + sigmaSq * x ^ 2) + (3/2) * (sigmaSq * x ^ 2) ≤
      3 * (sigmaSq + EZ) * x ^ 2 := by
    nlinarith [mul_nonneg hs0 (sq_nonneg x), mul_nonneg hEZ0 (sq_nonneg x),
      sq_nonneg x, mul_nonneg (mul_nonneg hs0 hx.le) (sq_nonneg x),
      mul_nonneg (mul_nonneg hEZ0 hx.le) hx.le]
  nlinarith [hk1, hk2, hφlog, hφx, hpoly, hψV]

/-! ### The fencing step -/

/-- Integrated differential inequality: `Λ(t)/t ≤ Λ(ε)/ε + 3(σ²+EZ)(t−ε)`. -/
theorem kr_lambda_le (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {ε t : ℝ} (hε : 0 < ε) (hεt : ε ≤ t) (ht4 : t ≤ 1/4) :
    Real.log (krF coeff (p : ℝ) t) / t ≤
      Real.log (krF coeff (p : ℝ) ε) / ε +
        3 * (sigmaSq + Ex (p : ℝ) (Zproc coeff (p : ℝ))) * (t - ε) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set κc := 3 * (sigmaSq + Ex (p : ℝ) (Zproc coeff (p : ℝ))) with hκdef
  set f : ℝ → ℝ := fun s => Real.log (krF coeff (p : ℝ) s) / s with hfdef
  have hcont : ContinuousOn f (Set.Icc ε t) := by
    apply ContinuousOn.div
    · apply ContinuousOn.log ((continuous_krF h0p h1p coeff).continuousOn)
      intro s _
      exact ne_of_gt (krF_pos h0p h1p coeff s)
    · exact continuousOn_id
    · intro s hs
      exact ne_of_gt (lt_of_lt_of_le hε hs.1)
  have hBcont : ContinuousOn (fun s => f ε + κc * (s - ε)) (Set.Icc ε t) :=
    (continuous_const.add (continuous_const.mul
      (continuous_id.sub continuous_const))).continuousOn
  have hB' : ∀ s ∈ Set.Ico ε t,
      HasDerivWithinAt (fun s => f ε + κc * (s - ε)) κc (Set.Ici s) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => f ε + κc * (s - ε)) κc s := by
      have h2 := (((hasDerivAt_id s).sub_const ε).const_mul κc).const_add (f ε)
      simpa using h2
    exact h1.hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Ico ε t, ∀ r, κc < r →
      ∃ᶠ z in nhdsWithin s (Set.Ioi s), slope f s z < r := by
    intro s hs r hr
    have hspos : 0 < s := lt_of_lt_of_le hε hs.1
    have hs4 : s ≤ 1/4 := le_trans hs.2.le ht4
    obtain ⟨D, hD, hDle⟩ := frozen_deriv_bound p hp coeff hB hVar hspos hs4
    have htend : Filter.Tendsto
        (slope (fun z => Real.log (krFrozen coeff (p : ℝ) s z) / z) s)
        (nhdsWithin s (Set.Ioi s)) (nhds D) :=
      (hasDerivAt_iff_tendsto_slope.mp hD).mono_left
        (nhdsWithin_mono s (fun z hz => ne_of_gt hz))
    have hev : ∀ᶠ z in nhdsWithin s (Set.Ioi s),
        slope (fun z => Real.log (krFrozen coeff (p : ℝ) s z) / z) s z < r :=
      htend.eventually_lt_const (lt_of_le_of_lt hDle hr)
    have hfinal : ∀ᶠ z in nhdsWithin s (Set.Ioi s), slope f s z < r := by
      filter_upwards [hev, self_mem_nhdsWithin] with z hz hzs
      have hsz : s < z := Set.mem_Ioi.mp hzs
      have hzpos : 0 < z := lt_trans hspos hsz
      have hle : f z ≤ Real.log (krFrozen coeff (p : ℝ) s z) / z := by
        apply (div_le_div_iff_of_pos_right hzpos).mpr
        exact Real.log_le_log (krF_pos h0p h1p coeff z)
          (krF_le_krFrozen h0p h1p coeff s z)
      have heq : f s = Real.log (krFrozen coeff (p : ℝ) s s) / s := by
        show Real.log (krF coeff (p : ℝ) s) / s = _
        rw [krFrozen_self]
      have hslopele : slope f s z ≤
          slope (fun z => Real.log (krFrozen coeff (p : ℝ) s z) / z) s z := by
        rw [slope_def_field, slope_def_field]
        apply (div_le_div_iff_of_pos_right
          (by linarith [hsz] : (0:ℝ) < z - s)).mpr
        linarith [hle, heq]
      linarith [hz]
    exact hfinal.frequently
  have hmain := image_le_of_liminf_slope_right_le_deriv_boundary
    (B' := fun _ => κc) hcont
    (show f ε ≤ f ε + κc * (ε - ε) by simp) hBcont hB' hbound
  have hend := hmain (Set.right_mem_Icc.mpr hεt)
  exact hend

/-! ### The Klein–Rio lower-tail cgf bound -/

/-- **T5a**: for `0 < t ≤ 1/4`,
`log Ex e^{−tZ} ≤ −t·EZ + 4·(σ² + EZ)·t²`. -/
theorem kr_lower_cgf (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ}
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 1/4) :
    Real.log (Ex (p : ℝ) (fun ω => Real.exp (-(t * Zproc coeff (p : ℝ) ω)))) ≤
      -(t * Ex (p : ℝ) (Zproc coeff (p : ℝ))) +
        4 * (sigmaSq + Ex (p : ℝ) (Zproc coeff (p : ℝ))) * t ^ 2 := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hEZ0 := Ex_Zproc_nonneg h0p h1p coeff
  have hs0 : 0 ≤ sigmaSq := sigmaSq_nonneg h0p h1p hVar
  set EZ := Ex (p : ℝ) (Zproc coeff (p : ℝ)) with hEZdef
  set κc := 3 * (sigmaSq + EZ) with hκdef
  set C₂ := Ex (p : ℝ) (fun ω => Zproc coeff (p : ℝ) ω ^ 2 *
    Real.exp |Zproc coeff (p : ℝ) ω|) with hC₂def
  have hC₂0 : 0 ≤ C₂ := Ex_nonneg h0p h1p fun ω => by positivity
  have hκc0 : 0 ≤ κc := by
    rw [hκdef]
    positivity
  have hΛdiv : Real.log (krF coeff (p : ℝ) t) / t ≤ -EZ + κc * t := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    set ε := min t (δ / (C₂ + 1)) with hεdef
    have hε0 : 0 < ε := lt_min ht (by positivity)
    have hεt : ε ≤ t := min_le_left _ _
    have h1 := kr_lambda_le p hp coeff hB hVar hε0 hεt ht4
    have h2 : Real.log (krF coeff (p : ℝ) ε) / ε ≤ -EZ + ε * C₂ := by
      have hFε := krF_le_Ex_exp_neg_tZ h0p h1p coeff hε0.le
      have hlog1 : Real.log (krF coeff (p : ℝ) ε) ≤
          Real.log (Ex (p : ℝ)
            (fun ω => Real.exp (-(ε * Zproc coeff (p : ℝ) ω)))) :=
        Real.log_le_log (krF_pos h0p h1p coeff ε) hFε
      have hcgf := cgf_neg_le_linear h0p h1p (Zproc coeff (p : ℝ)) hε0.le
        (le_trans hεt (by linarith))
      have h3 : Real.log (krF coeff (p : ℝ) ε) ≤ -(ε * EZ) + ε ^ 2 * C₂ :=
        le_trans hlog1 hcgf
      rw [div_le_iff₀ hε0]
      calc Real.log (krF coeff (p : ℝ) ε) ≤ -(ε * EZ) + ε ^ 2 * C₂ := h3
        _ = (-EZ + ε * C₂) * ε := by ring
    have hεC : ε * C₂ ≤ δ := by
      calc ε * C₂ ≤ (δ / (C₂ + 1)) * C₂ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hC₂0
        _ ≤ δ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < C₂ + 1)]
          nlinarith [hδ.le, hC₂0]
    have hκε : 0 ≤ κc * ε := mul_nonneg hκc0 hε0.le
    have hexpand : κc * (t - ε) = κc * t - κc * ε := by ring
    linarith [h1, h2]
  have hΛ : Real.log (krF coeff (p : ℝ) t) ≤ (-EZ + κc * t) * t := by
    rw [div_le_iff₀ ht] at hΛdiv
    exact hΛdiv
  have htr := Ex_exp_neg_tZ_le h0p h1p coeff ht.le
  have hExpos : 0 < Ex (p : ℝ)
      (fun ω => Real.exp (-(t * Zproc coeff (p : ℝ) ω))) :=
    Ex_pos h0p h1p fun ω => Real.exp_pos _
  have hlog := Real.log_le_log hExpos htr
  rw [Real.log_mul (ne_of_gt (krF_pos h0p h1p coeff t)) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  have hLmax := Lmax_le h0p h1p hB hVar ht.le ht4
  nlinarith [hlog, hΛ, hLmax, mul_nonneg hEZ0 (sq_nonneg t)]

end TalagrandCore
end

/-! ## Component: KRTail -/
section
/-
Klein–Rio lower-tail bound for the linear process: from the cgf bound
(`kr_lower_cgf`) via Chernoff in the small-deviation regime, and via the
single-branch Bennett bound in the large-deviation regime.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-- Log concavity: `c·log(1+x) ≤ log(1+c·x)` for `0 ≤ c ≤ 1`, `x ≥ 0`. -/
theorem log_one_add_mul_ge_of_le_one {c x : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hx : 0 ≤ x) :
    c * Real.log (1 + x) ≤ Real.log (1 + c * x) := by
  rcases hc0.eq_or_lt with hc | hc
  · simp [← hc]
  · exact log_one_add_mul_ge c x hc hc1 hx

/-- Chernoff transfer: the lower-tail indicator is dominated by the tilted mgf. -/
theorem chernoff_lower (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    {t u : ℝ} (ht : 0 ≤ t) :
    Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ Ex (p : ℝ) (Zproc coeff (p : ℝ)) - u then (1:ℝ) else 0) ≤
      Real.exp (t * (Ex (p : ℝ) (Zproc coeff (p : ℝ)) - u)) *
        Ex (p : ℝ) (fun ω => Real.exp (-(t * Zproc coeff (p : ℝ) ω))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  set EZ := Ex (p : ℝ) (Zproc coeff (p : ℝ)) with hEZdef
  have hpt : ∀ ω : κ → Bool,
      (if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0) ≤
        Real.exp (t * (EZ - u)) * Real.exp (-(t * Zproc coeff (p : ℝ) ω)) := by
    intro ω
    by_cases hcase : Zproc coeff (p : ℝ) ω ≤ EZ - u
    · rw [if_pos hcase, ← Real.exp_add]
      have harg : 0 ≤ t * (EZ - u) + -(t * Zproc coeff (p : ℝ) ω) := by
        have := mul_le_mul_of_nonneg_left hcase ht
        nlinarith
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ _ := Real.exp_le_exp.mpr harg
    · rw [if_neg hcase]
      positivity
  calc Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0)
      ≤ Ex (p : ℝ) (fun ω =>
          Real.exp (t * (EZ - u)) * Real.exp (-(t * Zproc coeff (p : ℝ) ω))) :=
        Ex_mono h0p h1p hpt
    _ = Real.exp (t * (EZ - u)) *
        Ex (p : ℝ) (fun ω => Real.exp (-(t * Zproc coeff (p : ℝ) ω))) :=
        Ex_smul _ _

/-- Branch domination: the tail of the sup is at most the tail of one branch. -/
theorem tail_le_branch_tail (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ) (a₀ : ι)
    {c : ℝ} :
    Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ c then (1:ℝ) else 0) ≤
      Ex (p : ℝ) (fun ω => if linSum coeff (p : ℝ) a₀ ω ≤ c then (1:ℝ) else 0) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  refine Ex_mono h0p h1p fun ω => ?_
  by_cases hcase : Zproc coeff (p : ℝ) ω ≤ c
  · have hlin : linSum coeff (p : ℝ) a₀ ω ≤ c :=
      le_trans (le_supProc (linSummand coeff (p : ℝ)) ω a₀) hcase
    rw [if_pos hcase, if_pos hlin]
  · rw [if_neg hcase]
    by_cases hlin : linSum coeff (p : ℝ) a₀ ω ≤ c
    · rw [if_pos hlin]; norm_num
    · rw [if_neg hlin]

/-- Klein–Rio lower-tail bound for the linear process. -/
theorem kr_lower_tail (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {w : ℝ} (hw : 0 < w)
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ w)
    (hEZ : Ex (p : ℝ) (Zproc coeff (p : ℝ)) ≤ w)
    {u : ℝ} (hu : 0 ≤ u) :
    Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ Ex (p : ℝ) (Zproc coeff (p : ℝ)) - u then (1:ℝ) else 0) ≤
      Real.exp (-((u / 32) * Real.log (1 + u / w))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hEZ0 : 0 ≤ Ex (p : ℝ) (Zproc coeff (p : ℝ)) := Ex_Zproc_nonneg h0p h1p coeff
  set EZ := Ex (p : ℝ) (Zproc coeff (p : ℝ)) with hEZdef
  rcases le_total u (4 * w) with hreg | hreg
  · -- Regime A: u ≤ 4w, Chernoff with t = u/(16w).
    rcases hu.eq_or_lt with hu0 | hu0
    · have hle1 : Ex (p : ℝ)
          (fun ω => if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0) ≤ 1 := by
        calc Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0)
            ≤ Ex (p : ℝ) (fun _ => (1:ℝ)) :=
              Ex_mono h0p h1p fun ω => by split <;> norm_num
          _ = 1 := Ex_const h0p h1p 1
      simpa [← hu0] using hle1
    · set t := u / (16 * w) with htdef
      have ht : 0 < t := div_pos hu0 (by positivity)
      have ht4 : t ≤ 1/4 := by
        rw [htdef, div_le_iff₀ (by positivity : (0:ℝ) < 16 * w)]
        linarith
      have hcgf := kr_lower_cgf p hp coeff hB (sigmaSq := w) hVar ht ht4
      have hMpos : 0 < Ex (p : ℝ) (fun ω => Real.exp (-(t * Zproc coeff (p : ℝ) ω))) :=
        Ex_pos h0p h1p fun ω => Real.exp_pos _
      have hMle : Ex (p : ℝ) (fun ω => Real.exp (-(t * Zproc coeff (p : ℝ) ω))) ≤
          Real.exp (-(t * EZ) + 4 * (w + EZ) * t ^ 2) := by
        have := Real.exp_le_exp.mpr hcgf
        rwa [Real.exp_log hMpos] at this
      have h2 : 4 * (w + EZ) * t ^ 2 ≤ 8 * w * t ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hEZ) (sq_nonneg t)]
      have h3 : -t * u + 8 * w * t ^ 2 = -(u ^ 2 / (32 * w)) := by
        rw [htdef]
        field_simp
        ring
      have hlog : Real.log (1 + u / w) ≤ u / w := by
        have h1p1 : (0:ℝ) < 1 + u / w := by positivity
        have := Real.log_le_sub_one_of_pos h1p1
        linarith
      have h4 : (u / 32) * Real.log (1 + u / w) ≤ u ^ 2 / (32 * w) := by
        have hm : (u / 32) * Real.log (1 + u / w) ≤ (u / 32) * (u / w) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        have heq : (u / 32) * (u / w) = u ^ 2 / (32 * w) := by ring
        linarith [heq ▸ hm]
      have hexp_le : t * (EZ - u) + (-(t * EZ) + 4 * (w + EZ) * t ^ 2) ≤
          -((u / 32) * Real.log (1 + u / w)) := by
        have hlin : t * (EZ - u) + (-(t * EZ) + 4 * (w + EZ) * t ^ 2) =
            -t * u + 4 * (w + EZ) * t ^ 2 := by ring
        linarith
      calc Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0)
          ≤ Real.exp (t * (EZ - u)) *
              Ex (p : ℝ) (fun ω => Real.exp (-(t * Zproc coeff (p : ℝ) ω))) :=
            chernoff_lower p hp coeff ht.le
        _ ≤ Real.exp (t * (EZ - u)) * Real.exp (-(t * EZ) + 4 * (w + EZ) * t ^ 2) :=
            mul_le_mul_of_nonneg_left hMle (Real.exp_pos _).le
        _ = Real.exp (t * (EZ - u) + (-(t * EZ) + 4 * (w + EZ) * t ^ 2)) :=
            (Real.exp_add _ _).symm
        _ ≤ Real.exp (-((u / 32) * Real.log (1 + u / w))) :=
            Real.exp_le_exp.mpr hexp_le
  · -- Regime B: 4w ≤ u, single-branch Bennett bound.
    have a₀ : ι := Classical.arbitrary ι
    have hthr : EZ - u ≤ -(3 * u / 4) := by linarith
    have hstep1 : Ex (p : ℝ)
        (fun ω => if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0) ≤
        Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ -(3 * u / 4) then (1:ℝ) else 0) := by
      refine Ex_mono h0p h1p fun ω => ?_
      by_cases hcase : Zproc coeff (p : ℝ) ω ≤ EZ - u
      · rw [if_pos hcase, if_pos (le_trans hcase hthr)]
      · rw [if_neg hcase]
        split <;> norm_num
    have hstep3 := bennett_lower_tail h0p h1p (hB a₀) hw (hVar a₀)
      (show (0:ℝ) ≤ 3 * u / 4 by linarith)
    have hxw : (0:ℝ) ≤ u / w := by positivity
    have hkey : (3/4 : ℝ) * Real.log (1 + u / w) ≤ Real.log (1 + 3 * u / 4 / w) := by
      have h := log_one_add_mul_ge_of_le_one (c := 3/4) (x := u / w)
        (by norm_num) (by norm_num) hxw
      have heq : (3/4 : ℝ) * (u / w) = 3 * u / 4 / w := by ring
      rwa [heq] at h
    have hlog0 : (0:ℝ) ≤ Real.log (1 + u / w) := Real.log_nonneg (by linarith)
    have hexp2 : (u / 32) * Real.log (1 + u / w) ≤
        3 * u / 4 / 2 * Real.log (1 + 3 * u / 4 / w) := by
      have h1 : 3 * u / 4 / 2 * ((3/4 : ℝ) * Real.log (1 + u / w)) ≤
          3 * u / 4 / 2 * Real.log (1 + 3 * u / 4 / w) :=
        mul_le_mul_of_nonneg_left hkey (by linarith)
      nlinarith [mul_nonneg hu hlog0]
    calc Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0)
        ≤ Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ -(3 * u / 4) then (1:ℝ) else 0) :=
          hstep1
      _ ≤ Ex (p : ℝ) (fun ω => if linSum coeff (p : ℝ) a₀ ω ≤ -(3 * u / 4) then (1:ℝ) else 0) :=
          tail_le_branch_tail p hp coeff a₀
      _ ≤ Real.exp (-((3 * u / 4 / 2) * Real.log (1 + 3 * u / 4 / w))) := hstep3
      _ ≤ Real.exp (-((u / 32) * Real.log (1 + u / w))) :=
          Real.exp_le_exp.mpr (neg_le_neg hexp2)

end TalagrandCore
end

/-! ## Component: Assembly -/
section
/-
Final assembly: the exact leaf statement of
`candes_romberg_talagrand_finite_bool_product_linear_process_bad_event_log_tail`,
from T4 (`poisson_upper_tail`), T5 (`kr_lower_tail`), T6
(`sigma2_expectation_bound`) and the Bridge.
-/

open MeasureTheory
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace TalagrandCore

section TwoSided

variable {κ ι : Type} [DecidableEq κ] [Fintype κ] [Fintype ι] [Nonempty ι]

/-- The two-sided sum-land tail bound, `B = 1`, denominator `σ² + EZ̄`. -/
theorem two_sided_tail (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ} (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {u : ℝ} (hu : 0 ≤ u)
    (hw : 0 < sigmaSq + Ex (p : ℝ) (Zbar coeff (p : ℝ))) :
    Ex (p : ℝ) (fun ω => if ¬ |Zproc coeff (p : ℝ) ω -
        Ex (p : ℝ) (Zproc coeff (p : ℝ))| ≤ u then (1:ℝ) else 0) ≤
      3 * Real.exp (-((u / 57600) *
        Real.log (1 + u / (sigmaSq + Ex (p : ℝ) (Zbar coeff (p : ℝ)))))) := by
  have h0p : (0:ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have h1p : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hEZbar0 : 0 ≤ Ex (p : ℝ) (Zbar coeff (p : ℝ)) :=
    Ex_nonneg h0p h1p fun ω => Zbar_nonneg coeff (p : ℝ) ω
  have hESig0 : 0 ≤ Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) :=
    Ex_nonneg h0p h1p fun ω => Sigma2_nonneg coeff (p : ℝ) ω
  set w := sigmaSq + Ex (p : ℝ) (Zbar coeff (p : ℝ)) with hwdef
  set w4 := sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
    Ex (p : ℝ) (Zbar coeff (p : ℝ)) with hw4def
  have hw4pos : 0 < w4 := by
    rw [hw4def]
    rw [hwdef] at hw
    linarith
  set EZ := Ex (p : ℝ) (Zproc coeff (p : ℝ)) with hEZdef
  set L := Real.log (1 + u / w) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by
    have : 0 ≤ u / w := div_nonneg hu hw.le
    linarith)
  -- pointwise two-sided split
  have hsplit : ∀ ω, (if ¬ |Zproc coeff (p : ℝ) ω - EZ| ≤ u then (1:ℝ) else 0) ≤
      (if EZ + u ≤ Zproc coeff (p : ℝ) ω then (1:ℝ) else 0) +
        (if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0) := by
    intro ω
    by_cases h : ¬ |Zproc coeff (p : ℝ) ω - EZ| ≤ u
    · rw [if_pos h]
      push_neg at h
      rcases le_total (Zproc coeff (p : ℝ) ω) EZ with hle | hge
      · have habs : |Zproc coeff (p : ℝ) ω - EZ| = EZ - Zproc coeff (p : ℝ) ω := by
          rw [abs_of_nonpos (by linarith)]
          ring
        rw [habs] at h
        have h2 : Zproc coeff (p : ℝ) ω ≤ EZ - u := by linarith
        rw [if_pos h2]
        have h3 : (0:ℝ) ≤ if EZ + u ≤ Zproc coeff (p : ℝ) ω then (1:ℝ) else 0 := by
          split <;> norm_num
        linarith
      · have habs : |Zproc coeff (p : ℝ) ω - EZ| = Zproc coeff (p : ℝ) ω - EZ :=
          abs_of_nonneg (by linarith)
        rw [habs] at h
        have h2 : EZ + u ≤ Zproc coeff (p : ℝ) ω := by linarith
        rw [if_pos h2]
        have h3 : (0:ℝ) ≤ if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0 := by
          split <;> norm_num
        linarith
    · rw [if_neg h]
      have h1 : (0:ℝ) ≤ if EZ + u ≤ Zproc coeff (p : ℝ) ω then (1:ℝ) else 0 := by
        split <;> norm_num
      have h2 : (0:ℝ) ≤ if Zproc coeff (p : ℝ) ω ≤ EZ - u then (1:ℝ) else 0 := by
        split <;> norm_num
      linarith
  have hsum := Ex_mono h0p h1p hsplit
  rw [Ex_add] at hsum
  -- upper tail via T4 + T6 absorption
  have hT6 := sigma2_expectation_bound p hp coeff hB sigmaSq hVar
  have hw49 : w4 ≤ 9 * w := by
    rw [hw4def, hwdef]
    linarith [hT6]
  have hupper : Ex (p : ℝ) (fun ω => if EZ + u ≤ Zproc coeff (p : ℝ) ω
      then (1:ℝ) else 0) ≤ 3 * Real.exp (-((u / 28800) * L)) := by
    have h := poisson_upper_tail p hp coeff hB hs hVar hu hw4pos
    refine le_trans h ?_
    have hlogchain : (u / 28800) * L ≤ (u / 3200) * Real.log (1 + u / w4) := by
      have hstep1 : Real.log (1 + u / (9 * w)) ≤ Real.log (1 + u / w4) := by
        apply Real.log_le_log (by positivity)
        have : u / (9 * w) ≤ u / w4 :=
          div_le_div_of_nonneg_left hu hw4pos hw49
        linarith
      have hstep2 : (1/9 : ℝ) * L ≤ Real.log (1 + u / (9 * w)) := by
        have h9 : u / (9 * w) = (1/9 : ℝ) * (u / w) := by
          field_simp
        rw [h9, hLdef]
        exact log_one_add_mul_ge (1/9) (u / w) (by norm_num) (by norm_num)
          (div_nonneg hu hw.le)
      have hu3200 : (0:ℝ) ≤ u / 3200 := by positivity
      calc (u / 28800) * L = (u / 3200) * ((1/9) * L) := by ring
        _ ≤ (u / 3200) * Real.log (1 + u / (9 * w)) :=
            mul_le_mul_of_nonneg_left hstep2 hu3200
        _ ≤ (u / 3200) * Real.log (1 + u / w4) :=
            mul_le_mul_of_nonneg_left hstep1 hu3200
    have := Real.exp_le_exp.mpr (neg_le_neg hlogchain)
    linarith
  -- lower tail via T5
  have hlower : Ex (p : ℝ) (fun ω => if Zproc coeff (p : ℝ) ω ≤ EZ - u
      then (1:ℝ) else 0) ≤ Real.exp (-((u / 28800) * L)) := by
    have hVarw : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ w := by
      intro a
      rw [hwdef]
      linarith [hVar a]
    have hEZw : EZ ≤ w := by
      have h1 : EZ ≤ Ex (p : ℝ) (Zbar coeff (p : ℝ)) :=
        Ex_mono h0p h1p fun ω => Zproc_le_Zbar coeff (p : ℝ) ω
      rw [hwdef]
      linarith
    have h := kr_lower_tail p hp coeff hB hw hVarw hEZw hu
    refine le_trans h (Real.exp_le_exp.mpr (neg_le_neg ?_))
    have : (u / 28800) * L ≤ (u / 32) * L := by
      apply mul_le_mul_of_nonneg_right _ hL0
      have : (0:ℝ) ≤ u := hu
      linarith [hu]
    linarith [this]
  -- combine and absorb the prefactor
  have hP1 : Ex (p : ℝ) (fun ω => if ¬ |Zproc coeff (p : ℝ) ω - EZ| ≤ u
      then (1:ℝ) else 0) ≤ 1 := by
    have hpt : ∀ ω, (if ¬ |Zproc coeff (p : ℝ) ω - EZ| ≤ u
        then (1:ℝ) else 0) ≤ 1 := by
      intro ω; split <;> norm_num
    calc Ex (p : ℝ) _ ≤ Ex (p : ℝ) (fun _ => (1:ℝ)) := Ex_mono h0p h1p hpt
      _ = 1 := Ex_const h0p h1p 1
  have hP4 : Ex (p : ℝ) (fun ω => if ¬ |Zproc coeff (p : ℝ) ω - EZ| ≤ u
      then (1:ℝ) else 0) ≤ 4 * Real.exp (-((u / 28800) * L)) := by
    calc Ex (p : ℝ) _ ≤ _ + _ := hsum
      _ ≤ 3 * Real.exp (-((u / 28800) * L)) +
          Real.exp (-((u / 28800) * L)) := add_le_add hupper hlower
      _ = 4 * Real.exp (-((u / 28800) * L)) := by ring
  have habs := prefactor_absorb
    (Ex (p : ℝ) (fun ω => if ¬ |Zproc coeff (p : ℝ) ω - EZ| ≤ u
      then (1:ℝ) else 0))
    4 ((u / 28800) * L) 2 hP1 hP4 (by norm_num)
    (mul_nonneg (by positivity) hL0) (by norm_num)
    (by
      have h43 : Real.log 4 ≤ 2 * Real.log 3 := by
        rw [show (2:ℝ) * Real.log 3 = Real.log (3^2) from by
          rw [Real.log_pow]; push_cast; ring]
        exact Real.log_le_log (by norm_num) (by norm_num)
      have h3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
      rw [div_le_iff₀ h3pos]
      linarith)
  refine le_trans habs (le_of_eq ?_)
  congr 1
  rw [hLdef]
  ring

end TwoSided

/-- **The leaf statement**, exactly as on the platform. -/
theorem candes_romberg_talagrand_leaf :
    ∃ K : ℝ, 0 < K ∧
      ∀ (κ : Type) [Fintype κ] (p : NNReal) (hp : p ≤ 1)
        (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → κ → ℝ) (B sigmaSq t : ℝ),
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ x : κ, |coeff a x| ≤ B) →
        (∀ a : ι,
          ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * (coeff a x) ^ 2 ≤ sigmaSq) →
        let boolProcess : ι → (κ → Bool) → ℝ :=
          fun a ω =>
            ∑ x : κ, ((cond (ω x) (1 : ℝ) 0 - (p : ℝ)) * coeff a x)
        let boolZ : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty
            (fun a : ι => boolProcess a ω)
        let boolZbar : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty
            (fun a : ι => |boolProcess a ω|)
        (Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)).real
            {ω | ¬ |boolZ ω -
                  (∫ ω, boolZ ω
                    ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)))| ≤ t} ≤
          3 * Real.exp
            (-(t / (K * B)) *
              Real.log
                (1 + (B * t) /
                  (sigmaSq + B *
                    (∫ ω, boolZbar ω
                      ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)))))) := by
  refine ⟨57600, by norm_num, ?_⟩
  intro κ _ p hp ι _ _ coeff B sigmaSq t hB0 hs ht hBc hVar
  intro boolProcess boolZ boolZbar
  classical
  -- identify the platform objects with the sum-land ones
  have hZ : boolZ = Zproc coeff (p : ℝ) := rfl
  have hZbar : boolZbar = Zbar coeff (p : ℝ) := rfl
  have hμ : (Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)) =
      bernPi κ p hp := rfl
  rw [hμ]
  -- rescaled data
  set coeff' : ι → κ → ℝ := fun a x => coeff a x / B with hcoeff'
  have hBne : B ≠ 0 := ne_of_gt hB0
  have hcoeff : coeff = fun a x => B * coeff' a x := by
    funext a x
    rw [hcoeff']
    field_simp
  have hB' : ∀ a x, |coeff' a x| ≤ 1 := by
    intro a x
    rw [hcoeff', abs_div, abs_of_pos hB0, div_le_one hB0]
    exact hBc a x
  have hVar' : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff' a x ^ 2 ≤
      sigmaSq / B ^ 2 := by
    intro a
    have hkey : ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff' a x ^ 2 =
        (∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2) / B ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hcoeff']
      field_simp
    rw [hkey]
    exact div_le_div_of_nonneg_right (hVar a) (by positivity)
  have hs' : 0 ≤ sigmaSq / B ^ 2 := by positivity
  -- scaling identities
  have hZscale : ∀ ω, Zproc coeff (p : ℝ) ω = B * Zproc coeff' (p : ℝ) ω := by
    intro ω
    conv_lhs => rw [hcoeff]
    exact Zproc_smul coeff' (p : ℝ) hB0.le ω
  have hZbarscale : ∀ ω, Zbar coeff (p : ℝ) ω = B * Zbar coeff' (p : ℝ) ω := by
    intro ω
    conv_lhs => rw [hcoeff]
    exact Zbar_smul coeff' (p : ℝ) hB0.le ω
  -- integrals to Ex
  have hIntZ : (∫ ω, boolZ ω ∂(bernPi κ p hp)) =
      B * Ex (p : ℝ) (Zproc coeff' (p : ℝ)) := by
    rw [hZ, integral_bernPi_eq_Ex]
    rw [Ex_congr hZscale, Ex_smul]
  have hIntZbar : (∫ ω, boolZbar ω ∂(bernPi κ p hp)) =
      B * Ex (p : ℝ) (Zbar coeff' (p : ℝ)) := by
    rw [hZbar, integral_bernPi_eq_Ex]
    rw [Ex_congr hZbarscale, Ex_smul]
  set EZ' := Ex (p : ℝ) (Zproc coeff' (p : ℝ)) with hEZ'
  set EZbar' := Ex (p : ℝ) (Zbar coeff' (p : ℝ)) with hEZbar'
  set w := sigmaSq / B ^ 2 + EZbar' with hwdef
  have hEZbar'0 : 0 ≤ EZbar' :=
    Ex_nonneg p.coe_nonneg (by exact_mod_cast hp)
      fun ω => Zbar_nonneg coeff' (p : ℝ) ω
  have hw0 : 0 ≤ w := by rw [hwdef]; linarith [hs']
  -- the denominator identity: sigmaSq + B·EZ̄ = B²·w
  have hdenom : sigmaSq + B * (B * EZbar') = B ^ 2 * w := by
    rw [hwdef]
    field_simp
  -- measure of the bad event ≤ Ex of the B=1 indicator
  have hmeas : (bernPi κ p hp).real
      {ω | ¬ |boolZ ω - (∫ ω, boolZ ω ∂(bernPi κ p hp))| ≤ t} ≤
      Ex (p : ℝ) (fun ω => if ¬ |Zproc coeff' (p : ℝ) ω - EZ'| ≤ t / B
        then (1:ℝ) else 0) := by
    rw [bernPi_real_eq_Ex_indicator]
    apply Ex_mono p.coe_nonneg (by exact_mod_cast hp)
    intro ω
    rw [Set.indicator_apply]
    split
    · rename_i hmem
      have hev : ¬ |Zproc coeff' (p : ℝ) ω - EZ'| ≤ t / B := by
        intro hcon
        apply hmem
        show |boolZ ω - (∫ ω, boolZ ω ∂(bernPi κ p hp))| ≤ t
        rw [hIntZ, hZ, hZscale ω]
        have habs : |B * Zproc coeff' (p : ℝ) ω - B * EZ'| =
            B * |Zproc coeff' (p : ℝ) ω - EZ'| := by
          rw [← mul_sub, abs_mul, abs_of_pos hB0]
        rw [habs]
        calc B * |Zproc coeff' (p : ℝ) ω - EZ'| ≤ B * (t / B) :=
              mul_le_mul_of_nonneg_left hcon hB0.le
          _ = t := by field_simp
      rw [if_pos hev]
    · split <;> norm_num
  -- case split on w
  rcases eq_or_lt_of_le hw0 with hweq | hwpos
  · -- w = 0: the bound is trivially ≥ 1
    have hdenom0 : sigmaSq + B * (∫ ω, boolZbar ω ∂(bernPi κ p hp)) = 0 := by
      rw [hIntZbar, hdenom, ← hweq]
      ring
    rw [hdenom0]
    rw [div_zero, add_zero, Real.log_one, mul_zero, Real.exp_zero, mul_one]
    calc (bernPi κ p hp).real _ ≤
        Ex (p : ℝ) (fun ω => if ¬ |Zproc coeff' (p : ℝ) ω - EZ'| ≤ t / B
          then (1:ℝ) else 0) := hmeas
      _ ≤ Ex (p : ℝ) (fun _ => (1:ℝ)) := by
          apply Ex_mono p.coe_nonneg (by exact_mod_cast hp)
          intro ω; split <;> norm_num
      _ = 1 := Ex_const p.coe_nonneg (by exact_mod_cast hp) 1
      _ ≤ 3 := by norm_num
  · -- w > 0: apply the two-sided bound
    have ht' : 0 ≤ t / B := div_nonneg ht hB0.le
    have hmain := two_sided_tail (κ := κ) (ι := ι) p hp coeff' hB' hs' hVar'
      ht' (by rw [← hwdef]; exact hwpos)
    have hfinal := le_trans hmeas hmain
    refine le_trans hfinal (le_of_eq ?_)
    congr 1
    rw [hIntZbar, hdenom]
    have harg2 : B * t / (B ^ 2 * w) = t / B / w := by
      rw [div_div]
      rw [show B ^ 2 * w = B * (B * w) from by ring]
      exact mul_div_mul_left t (B * w) hBne
    rw [harg2]
    have harg1 : -(t / B / 57600 * Real.log (1 + t / B / w)) =
        -(t / (57600 * B)) * Real.log (1 + t / B / w) := by
      rw [div_div]
      ring
    rw [← harg1]

end TalagrandCore
end

open MatrixCompletion
open MeasureTheory
open scoped Classical BigOperators

theorem solution :
    ∃ K : ℝ, 0 < K ∧
      ∀ (κ : Type) [Fintype κ] (p : NNReal) (hp : p ≤ 1)
        (ι : Type) [Fintype ι] [Nonempty ι]
        (coeff : ι → κ → ℝ) (B sigmaSq t : ℝ),
        0 < B → 0 ≤ sigmaSq → 0 ≤ t →
        (∀ a : ι, ∀ x : κ, |coeff a x| ≤ B) →
        (∀ a : ι,
          ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * (coeff a x) ^ 2 ≤ sigmaSq) →
        let boolProcess : ι → (κ → Bool) → ℝ :=
          fun a ω =>
            ∑ x : κ, ((cond (ω x) (1 : ℝ) 0 - (p : ℝ)) * coeff a x)
        let boolZ : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => boolProcess a ω)
        let boolZbar : (κ → Bool) → ℝ :=
          fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a : ι => |boolProcess a ω|)
        (Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)).real
            {ω | ¬ |boolZ ω -
                  (∫ ω, boolZ ω
                    ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)))| ≤ t} ≤
          3 * Real.exp
            (-(t / (K * B)) *
              Real.log
                (1 + (B * t) /
                  (sigmaSq + B *
                    (∫ ω, boolZbar ω
                      ∂(Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure))))))
  := TalagrandCore.candes_romberg_talagrand_leaf
