-- Prove2me | solution 1 for TalagrandCore.poisson_tail
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T05:17:29.272683+00:00
-- url     : https://prove2.me/submissions/65c5bbd0-e2ac-4979-9152-9779058fd63c

import Definitions.Def_talagrand_finite_bool_core
import Theorems.Thm_entropy_n_coordinate_han_subadditivity_measure_pi_pos

import Theorems.Thm_TalagrandCore_entropy_tensor_psi
import Theorems.Thm_TalagrandCore_selfbounding_exp_bound
import Theorems.Thm_TalagrandCore_per_coord_bound
import Theorems.Thm_TalagrandCore_two_copy_entropy_Z
import Theorems.Thm_TalagrandCore_sigma2_weighted_exp

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
        exact this.congr_deriv (by field_simp; ring)
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
        exact this.congr_deriv (by ring)
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
        exact this.congr_deriv (by ring)
      have := hlog1.sub hlog2
      exact this.congr_deriv (by ring))
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
    simpa [linSummand, Zproc] using this
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
  have hsum := HasDerivAt.sum this
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun l => ?_)
  simp [Finset.sum_apply]

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
        exact ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).congr_deriv (by ring)
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
        exact ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).congr_deriv (by ring)
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

open TalagrandCore
variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem solution (p : NNReal) (hp : p ≤ 1)
    (g : ι → κ → Bool → ℝ) (hg0 : ∀ a x b, 0 ≤ g a x b)
    (hg1 : ∀ a x b, g a x b ≤ 1) {m s : ℝ}
    (hm : Ex (p : ℝ) (fun ω => supProc g ω) ≤ m) (hm0 : 0 < m) (hms : m ≤ s) :
    Ex (p : ℝ) (fun ω => if s ≤ supProc g ω then (1:ℝ) else 0) ≤
      Real.exp (-(s * Real.log (s / m) - s + m)) := by
  apply TalagrandCore.poisson_tail <;> assumption
