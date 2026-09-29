-- Prove2me | solution 1 for TalagrandCore.entropy_tensor_psi
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T05:09:02.690681+00:00
-- url     : https://prove2.me/submissions/9c7a6892-1b2a-47ea-a066-eec7dd43b248

import Definitions.Def_talagrand_finite_bool_core
import Theorems.Thm_entropy_n_coordinate_han_subadditivity_measure_pi_pos


open MeasureTheory
open scoped Classical BigOperators

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
        exact ((Real.hasDerivAt_log h1.ne').comp x hin).congr_deriv (by ring)
      have hq : HasDerivAt (fun y : ℝ => 2 * y / (2 + y)) (4 / (2 + x) ^ 2) x := by
        have hnum : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
          simpa using (hasDerivAt_id x).const_mul (2:ℝ)
        have hden : HasDerivAt (fun y : ℝ => 2 + y) 1 x := (hasDerivAt_id x).const_add 2
        have := hnum.div hden h2.ne'
        refine this.congr_deriv ?_
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring
      exact hlog.sub hq)
    (by norm_num)
    (fun x hx => by
      have h1 : (0:ℝ) < 1 + x := by linarith
      have h2 : (0:ℝ) < 2 + x := by linarith
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) h1]
      nlinarith [sq_nonneg x])
    u hu
  linarith [key]

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
        have := (Real.hasDerivAt_log h1c.ne').comp x hin
        exact this.congr_deriv (by ring)
      have hlog2 : HasDerivAt (fun y : ℝ => Real.log (1 + y) / c) ((1 / (1 + x)) / c) x := by
        have hin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
        have := ((Real.hasDerivAt_log h1.ne').comp x hin).div_const c
        simpa using this
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
        have := (Real.hasDerivAt_log h1s.ne').comp x hin
        exact this.congr_deriv (by ring)
      have hlog2 : HasDerivAt (fun y : ℝ => s * Real.log (1 + y)) (s * (1 / (1 + x))) x := by
        have hin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
        have := ((Real.hasDerivAt_log h1.ne').comp x hin).const_mul s
        simpa using this
      have := hlog1.sub hlog2
      refine this.congr_deriv ?_
      ring)
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
      (fun η => by (try simp only); rw [hinner η])
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
        (fun η => by (try simp only); rw [hinner η])
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

open TalagrandCore
variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem solution (p : NNReal) (hp : p ≤ 1)
    (Z : (κ → Bool) → ℝ) (lam : ℝ)
    (c : κ → (κ → Bool) → ℝ) (hc : ∀ x, FiberConst x (c x)) :
    lam * Ex (p : ℝ) (fun ω => Z ω * Real.exp (lam * Z ω)) -
      Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω)) *
        Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * Z ω))) ≤
      ∑ x : κ, Ex (p : ℝ)
        (fun ω => Real.exp (lam * Z ω) * psi (lam * (Z ω - c x ω))) := by
  apply TalagrandCore.entropy_tensor_psi <;> assumption
