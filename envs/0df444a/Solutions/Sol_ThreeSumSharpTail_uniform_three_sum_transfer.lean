-- Prove2me | solution 1 for ThreeSumSharpTail.uniform_three_sum_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T18:55:27.451969+00:00
-- url     : https://prove2.me/submissions/48c7ce78-8c45-44e0-b1d9-ae2595267ec7

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Corollary15_16
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_ThreeSumSource_ReductionClaims
import Theorems.Thm_Light_Sec3_ChanHe_claim_CH20_Theorem_5_1
import Theorems.Thm_Light_Sec3_claim_VW13_Theorem_4_3
import Theorems.Thm_Light_Sec3_realized_threeSum
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_endStatement
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter Asymptotics

section


/-!
# Bounds up to a constant factor, in several parameters

The paper writes `f = O(g)` for functions of several parameters that are tied by side conditions,
such as `D ^ 18 ≤ n` for the parameters `n`, `D`, `w`. `Dominated dom f g` says this: there is a
constant `C ≥ 0` with `f x ≤ C * g x` for every tuple `x` of parameters that satisfies `dom x`. If
there is no side condition, `dom` is `fun _ => True`. The type `α` of the parameters is best a
structure with one named field for each of them, so that a bound reads
`Dominated (fun p => p.D ^ 18 ≤ p.n) (fun p => cost p) fun p => p.n ^ 2 / p.D`.

The lemmas of this file are the steps that the paper takes without comment: such bounds can be
chained (`Dominated.trans`), added (`Dominated.add`, `Dominated.add_add`), multiplied and divided
(`Dominated.mul`, `Dominated.mul_left`, `Dominated.const_mul`, `Dominated.pow`,
`Dominated.div_right`), joined by a case distinction (`Dominated.ite`), restricted to a smaller
domain (`Dominated.mono_dom`) and specialized (`Dominated.comp`). With them no proof has to name a
constant. A bound enters the calculus by `Dominated.of_le`, `Dominated.of_le_const_mul` or
`Dominated.of_exists_const`, and leaves it by `obtain ⟨C, hC, hle⟩` or `Dominated.exists_const_and`.
For functions of one natural number, `Dominated.of_eventually` takes a bound for all large `n`,
`Dominated.isBigO` gives Mathlib's `f =O[atTop] g`, and `isBigO_comp_add_one` substitutes a size
that need not tend to infinity.

In every closure lemma the bound comes first and the side conditions follow.

For nonnegative `f` and `g` the notion is Mathlib's `f =O[𝓟 {x | dom x}] g`, big-O along the
principal filter of the domain (`dominated_iff_isBigO_principal`). The one-sided form is taken
because a running time is bounded from above only.

## The notions of "bounded up to a constant" in this library

* `f =O[atTop] g` of Mathlib bounds `|f|` for large `n`. In this sense `IsBigOPow f a` is `O(n^a)`,
  `IsPowPolylog f a` is `O(n^a (log n)^e)` for some `e`, and `IsPowLittleO f a` is `n^{a+o(1)}`.
  The exponents of the theorems are stated with them.
* `UpperBigOPow`, `UpperPowPolylog` and `UpperPowLittleO` are the same three classes as bounds on
  `f` and not on `|f|`, for running times. A two-sided bound gives the one-sided one
  (`IsBigOPow.upperBigOPow`, `IsPowPolylog.upperPowPolylog`, `IsPowLittleO.upperPowLittleO`).
* `Dominated dom f g` bounds `f` on the whole domain, for several parameters. It comes from a bound
  for large `n` by `Dominated.of_eventually` and gives one by `Dominated.isBigO`.
* `Scale.SoftO t e` says that a count `t` with values in `ℕ` is `Dominated` by a monomial with the
  exponents `e`, up to powers of one more quantity; the tactic `growth` reads the exponents off an
  explicit expression. It gives a `Dominated` bound by `Scale.SoftO.dominated`. Its instance
  `SoftOSqrtPow` gives `IsPowPolylog` by `SoftOSqrtPow.isPowPolylog`.
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp






namespace Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/

/-- A bound with an explicit nonnegative constant. -/
theorem of_le_const_mul {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ x, dom x → f x ≤ C * g x) :
    Dominated dom f g :=
  ⟨C, hC, hfg⟩

/-- A bound with constant one. -/
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩





/-- A bound with a constant of unknown sign, when `g` is nonnegative on the domain. -/
theorem of_exists_const (hfg : ∃ C : ℝ, ∀ x, dom x → f x ≤ C * g x) (hg : ∀ x, dom x → 0 ≤ g x) :
    Dominated dom f g := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨|C|, abs_nonneg C, fun x hx =>
    (hC x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hg x hx))⟩













/-! ### Leaving the calculus -/



/-! ### Chaining, restricting, substituting -/

/-- `f = O(g)` and `g = O(h)` give `f = O(h)`. -/
protected theorem trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => (hf x hx).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x hx) hC

/-- A bound holds on every smaller domain. -/
theorem mono_dom (hfg : Dominated dom f g) (hdom : ∀ x, dom' x → dom x) : Dominated dom' f g := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun x hx => hf x (hdom x hx)⟩

/-- The left side may be replaced by a smaller function. -/
theorem mono_left (hfg : Dominated dom f g) (hle : ∀ x, dom x → f' x ≤ f x) : Dominated dom f' g :=
  (of_le hle).trans hfg

/-- The right side may be replaced by a larger function. -/
theorem mono_right (hfg : Dominated dom f g) (hle : ∀ x, dom x → g x ≤ g' x) : Dominated dom f g' :=
  hfg.trans (of_le hle)

/-- Both sides may be replaced by functions that agree with them on the domain. -/
protected theorem congr (hfg : Dominated dom f g) (hf : ∀ x, dom x → f x = f' x)
    (hg : ∀ x, dom x → g x = g' x) : Dominated dom f' g' :=
  (hfg.mono_left fun x hx => (hf x hx).ge).mono_right fun x hx => (hg x hx).le

/-- Substituting the parameters: a bound in `x` gives a bound in `y` at `x = φ y`, on every domain
that `φ` maps into `dom`. -/
protected theorem comp (hfg : Dominated dom f g) (φ : β → α) {dom' : β → Prop}
    (hφ : ∀ y, dom' y → dom (φ y)) : Dominated dom' (fun y => f (φ y)) fun y => g (φ y) := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun y hy => hf (φ y) (hφ y hy)⟩

/-! ### Sums and case distinctions -/

/-- `O(h) + O(h) = O(h)`. -/
protected theorem add (hf : Dominated dom f h) (hg : Dominated dom g h) :
    Dominated dom (fun x => f x + g x) h := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  rw [add_mul]
  exact add_le_add (hf x hx) (hg x hx)









/-! ### Products and quotients -/

/-- A nonnegative constant factor on the left side is absorbed. -/
theorem const_mul (hfg : Dominated dom f g) {c : ℝ} (hc : 0 ≤ c) :
    Dominated dom (fun x => c * f x) g := by
  obtain ⟨C, hC, hf⟩ := hfg
  refine ⟨c * C, mul_nonneg hc hC, fun x hx => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x hx) hc






/-- A constant factor of any sign in front of a function that is nonnegative on the domain is
absorbed. -/
theorem const_mul_of_nonneg (hfg : Dominated dom f g) (c : ℝ) (hf : ∀ x, dom x → 0 ≤ f x) :
    Dominated dom (fun x => c * f x) g :=
  (of_exists_const ⟨c, fun _ _ => le_rfl⟩ hf).trans hfg

/-- Both sides may be multiplied from the left by a function that is nonnegative on the domain. -/
theorem mul_left (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => k x * f x) fun x => k x * g x := by
  obtain ⟨C, hC, hf⟩ := hfg
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hf x hx) (hk x hx)

/-- Both sides may be multiplied from the right by a function that is nonnegative on the domain. -/
theorem mul_right (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => f x * k x) fun x => g x * k x := by
  simpa only [mul_comm] using hfg.mul_left hk








/-- `O(g) ^ e = O(g ^ e)` for nonnegative `f`. -/
protected theorem pow (hfg : Dominated dom f g) (hf : ∀ x, dom x → 0 ≤ f x) (e : ℕ) :
    Dominated dom (fun x => f x ^ e) fun x => g x ^ e := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine ⟨C ^ e, pow_nonneg hC e, fun x hx => ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ (hf x hx) (hle x hx) e

/-! ### Functions of one natural number -/






















/-- A bound by a nonnegative `g` that holds from some unknown point on gives a bound by `g + 1`
everywhere. -/
theorem of_eventually_add_one {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n)
    (hg : ∀ n, 0 ≤ g n) : Dominated (fun _ => True) f fun n => g n + 1 := by
  have hpos : ∀ n, 0 ≤ n → 0 < g n + 1 := fun n _ => add_pos_of_nonneg_of_pos (hg n) zero_lt_one
  refine (of_eventually (C := |C|) (hfg.mono fun n hn => hn.trans ?_) hpos).mono_dom
    fun n _ => n.zero_le
  exact (mul_le_mul_of_nonneg_right (le_abs_self C) (hg n)).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg C))

/-- A bound on `|f|` from some point on is Mathlib's `f =O[atTop] g`. -/
theorem isBigO {f g : ℕ → ℝ} {n₀ : ℕ} (hfg : Dominated (fun n => n₀ ≤ n) (fun n => |f n|) g) :
    f =O[atTop] g := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine IsBigO.of_bound C (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hle n hn).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)

end Dominated

/-- If `G = O(g)` with `g ≥ 0`, then `G(size n) = O(g(size n) + 1)` for every `size : ℕ → ℕ`. The
sizes need not tend to infinity; the `+ 1` covers the finitely many sizes at which the bound does
not hold yet. -/
theorem isBigO_comp_add_one {G g : ℕ → ℝ} (hG : G =O[atTop] g) (hg : ∀ s, 0 ≤ g s)
    (size : ℕ → ℕ) : (fun n => G (size n)) =O[atTop] fun n => g (size n) + 1 := by
  obtain ⟨C, hC⟩ := hG.bound
  have hall : Dominated (fun _ => True) (fun s => |G s|) fun s => g s + 1 :=
    .of_eventually_add_one (C := C) (hC.mono fun s hs => by
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hg s)] at hs) hg
  exact Dominated.isBigO (n₀ := 0) (hall.comp size fun _ _ => trivial)

end ThreeSumApsp

end
end


section

public section
open Filter Asymptotics
namespace ThreeSumApsp

theorem isBigO_of_abs_le {f g : ℕ → ℝ} (C : ℝ) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → |f n| ≤ C * g n) :
    f =O[atTop] g := by
  refine IsBigO.of_bound |C| (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul]
  exact (h n hn).trans (le_abs_self _)










/-- `n ^ a = O(n ^ b)` for `a ≤ b`. -/
theorem isBigO_rpow_rpow_of_le {a b : ℝ} (hab : a ≤ b) :
    (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  refine isBigO_of_abs_le 1 1 fun n hn => ?_
  rw [one_mul, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)]
  exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hab

/-- `n ^ a * n ^ b = n ^ (a + b)` for all large `n`. -/
theorem rpow_mul_rpow_eventuallyEq (a b : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ b) =ᶠ[atTop] fun n : ℕ => (n : ℝ) ^ (a + b) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_add (Nat.cast_pos.2 hn)]

/-- `(log n) ^ e = o(n ^ η)` for `η > 0`. -/
theorem isLittleO_log_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    (fun n : ℕ => Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ η := by
  have h := (isLittleO_log_rpow_rpow_atTop (e : ℝ) hη).comp_tendsto tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast] using h

/-- `(log n) ^ e = O((log n) ^ e')` for `e ≤ e'`. -/
theorem isBigO_log_pow_log_pow_of_le {e e' : ℕ} (he : e ≤ e') :
    (fun n : ℕ => Real.log n ^ e) =O[atTop] fun n : ℕ => Real.log n ^ e' := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hlog
  refine isBigO_of_abs_le 1 n₀ fun n hn => ?_
  rw [one_mul, abs_of_nonneg (pow_nonneg (zero_le_one.trans (hn₀ n hn)) e)]
  exact pow_le_pow_right₀ (hn₀ n hn) he

/-- `n ^ a * (log n) ^ e = O(n ^ b * (log n) ^ e')` for `a ≤ b` and `e ≤ e'`. -/
theorem isBigO_rpow_mul_log_pow_of_le {a b : ℝ} {e e' : ℕ} (hab : a ≤ b) (he : e ≤ e') :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ b * Real.log n ^ e' :=
  (isBigO_rpow_rpow_of_le hab).mul (isBigO_log_pow_log_pow_of_le he)

/-- Logarithms are absorbed: `n ^ a * (log n) ^ e = o(n ^ b)` for `a < b`. -/
theorem isLittleO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a) atTop).mul_isLittleO
    (isLittleO_log_pow_rpow (sub_pos.2 hab) e)
  refine h.congr' EventuallyEq.rfl ?_
  simpa only [add_sub_cancel] using rpow_mul_rpow_eventuallyEq a (b - a)






/-- Constants are absorbed as well: `C * (n ^ a * (log n) ^ e) ≤ n ^ b` for all large `n`, if
`a < b`. -/
theorem eventually_mul_rpow_mul_log_pow_le (C : ℝ) {a b : ℝ} (hab : a < b) (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) ^ a * Real.log n ^ e) ≤ (n : ℝ) ^ b := by
  have h := ((isLittleO_rpow_mul_log_pow_rpow hab e).const_mul_left C).def zero_lt_one
  filter_upwards [h] with n hn
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg b)] at hn
  exact (le_abs_self _).trans hn

/-- `C * n ^ a ≤ n ^ b` for all large `n`, if `a < b`. -/
theorem eventually_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  simpa only [pow_zero, mul_one] using eventually_mul_rpow_mul_log_pow_le C hab 0

theorem isBigO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ b :=
  (isLittleO_rpow_mul_log_pow_rpow hab e).isBigO

end ThreeSumApsp

end
end

section


/-!
# Calculating with `O(n^a)` and `Õ(n^a)`

Closure properties of the two classes `IsBigOPow f a`, that is `f(n) = O(n^a)`, and
`IsPowPolylog f a`, that is `f(n) = O(n^a (log n)^{O(1)})`, which the paper writes `Õ(n^a)`.

A bound enters by `of_abs_le`, by `of_isBigO`, or from the model functions (`isBigOPow_rpow`,
`isBigOPow_natCast_pow`, `isBigOPow_const`, `isPowPolylog_rpow_mul_log_pow`, `isPowPolylog_log_pow`,
and for rounded powers `isBigOPow_ceil_rpow`, `isBigOPow_floor_rpow` and their inverses;
`IsBigOPow.natCeil` for rounding in general). Both classes are closed under sums, constant factors
and passing to a smaller function (`mono_left`). A product has the exponent `a + b` and a power the
exponent `a * k` (`pow`, `rpow`), to be brought to the wanted form by `mono`, which asks only for an
inequality between exponents. Substituting `n ↦ size n` multiplies nonnegative exponents
(`IsBigOPow.comp`, `IsPowPolylog.comp`), for `size n = O(n^μ)`, and then `log (size n) = Õ(1)`
(`IsBigOPow.isPowPolylog_log_natCast`). The classes are related by `IsBigOPow.isPowPolylog` and,
with a loss in the exponent, `IsPowPolylog.isBigOPow`; `eventually_abs_le` absorbs the constant as
well.
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` -/

/-- `n ^ a = O(n^a)`. -/
theorem isBigOPow_rpow (a : ℝ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ a) a :=
  isBigO_refl _ _

/-- `n ^ k = O(n^k)` for a natural number `k`. -/
theorem isBigOPow_natCast_pow (k : ℕ) : IsBigOPow (fun n : ℕ => (n : ℝ) ^ k) k := by
  simpa only [Real.rpow_natCast] using isBigOPow_rpow (k : ℝ)





/-- A constant is `O(n^0)`. -/
theorem isBigOPow_const (c : ℝ) : IsBigOPow (fun _ => c) 0 :=
  isBigO_of_abs_le |c| 0 fun n _ => by rw [Real.rpow_zero, mul_one]

namespace IsBigOPow





/-- If `g = O(n^a)` and `f = O(g)`, then `f = O(n^a)`. -/
theorem of_isBigO (hg : IsBigOPow g a) (hfg : f =O[atTop] g) : IsBigOPow f a :=
  hfg.trans hg

/-- If `|f n| ≤ |g n|` for all large `n` and `g = O(n^a)`, then `f = O(n^a)`. -/
theorem mono_left (hg : IsBigOPow g a) (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : IsBigOPow f a :=
  hg.of_isBigO (IsBigO.of_bound' h)

/-- If `0 ≤ f n ≤ g n` for all large `n` and `g = O(n^a)`, then `f = O(n^a)`. -/
theorem mono_left_of_nonneg (hg : IsBigOPow g a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : IsBigOPow f a :=
  hg.mono_left ((h0.and h).mono fun _ hn => abs_le_abs_of_nonneg hn.1 hn.2)

/-- The exponent may be raised. -/
protected theorem mono (hf : IsBigOPow f a) (hab : a ≤ b) : IsBigOPow f b :=
  hf.trans (isBigO_rpow_rpow_of_le hab)

/-- Products of polynomially bounded functions add their exponents. -/
protected theorem mul (hf : IsBigOPow f a) (hg : IsBigOPow g b) :
    IsBigOPow (fun n => f n * g n) (a + b) :=
  (IsBigO.mul hf hg).congr' EventuallyEq.rfl (rpow_mul_rpow_eventuallyEq a b)

/-- `O(n^a) + O(n^a) = O(n^a)`. -/
protected theorem add (hf : IsBigOPow f a) (hg : IsBigOPow g a) :
    IsBigOPow (fun n => f n + g n) a :=
  IsBigO.add hf hg






/-- `O(n^a) ^ r = O(n^(a r))` for a real exponent `r ≥ 0`. -/
protected theorem rpow (hf : IsBigOPow f a) {r : ℝ} (hr : 0 ≤ r) :
    IsBigOPow (fun n => f n ^ r) (a * r) := by
  have h := IsBigO.rpow hr (Eventually.of_forall fun n : ℕ => Real.rpow_nonneg n.cast_nonneg a) hf
  exact h.congr_right fun n => (Real.rpow_mul n.cast_nonneg a r).symm









/-- If `f = O(n^a)` then `|f| = O(n^a)`. -/
protected theorem abs (hf : IsBigOPow f a) : IsBigOPow (fun n => |f n|) a :=
  IsBigO.norm_left hf

/-- The constant is absorbed: if `f = O(n^a)` and `a < b`, then `|f n| ≤ n ^ b` for all large `n`.
-/
theorem eventually_abs_le (hf : IsBigOPow f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by
  obtain ⟨C, hC⟩ := IsBigO.bound hf
  filter_upwards [hC, eventually_mul_rpow_le C hab] with n hn hCn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)] at hn
  exact hn.trans hCn

/-- `O(n^a) ⊆ Õ(n^a)`. -/
theorem isPowPolylog (hf : IsBigOPow f a) : IsPowPolylog f a :=
  ⟨0, by simpa only [pow_zero, mul_one, IsBigOPow] using hf⟩

end IsBigOPow

/-- Rounding up keeps the class: if `f = O(n^a)` with `a ≥ 0`, then `⌈f n⌉ = O(n^a)`. -/
theorem IsBigOPow.natCeil (hf : IsBigOPow f a) (ha : 0 ≤ a) :
    IsBigOPow (fun n => (⌈f n⌉₊ : ℝ)) a := by
  refine (hf.abs.add ((isBigOPow_const 1).mono ha)).mono_left_of_nonneg
    (Eventually.of_forall fun n => Nat.cast_nonneg _) (Eventually.of_forall fun n => ?_)
  obtain hneg | hpos := le_or_gt (f n) 0
  · rw [Nat.ceil_eq_zero.2 hneg, Nat.cast_zero]
    positivity
  · exact (Nat.ceil_lt_add_one hpos.le).le.trans (add_le_add_left (le_abs_self _) 1)

/-- `⌈n ^ μ⌉ = O(n^μ)` for `μ ≥ 0`. -/
theorem isBigOPow_ceil_rpow {μ : ℝ} (hμ : 0 ≤ μ) :
    IsBigOPow (fun n : ℕ => (⌈(n : ℝ) ^ μ⌉₊ : ℝ)) μ :=
  (isBigOPow_rpow μ).natCeil hμ

























/-! ### `Õ(n^a)` -/











/-- `n ^ a = Õ(n^a)`. -/
theorem isPowPolylog_rpow (a : ℝ) : IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a) a :=
  (isBigOPow_rpow a).isPowPolylog

/-- `(log n) ^ e = Õ(1)`. -/
theorem isPowPolylog_log_pow (e : ℕ) : IsPowPolylog (fun n : ℕ => Real.log n ^ e) 0 :=
  ⟨e, by simpa only [Real.rpow_zero, one_mul] using isBigO_refl (fun n : ℕ => Real.log n ^ e) atTop⟩

/-- `log n = Õ(1)`. -/
theorem isPowPolylog_log : IsPowPolylog (fun n : ℕ => Real.log n) 0 := by
  simpa only [pow_one] using isPowPolylog_log_pow 1

/-- A constant is `Õ(1)`. -/
theorem isPowPolylog_const (c : ℝ) : IsPowPolylog (fun _ => c) 0 :=
  (isBigOPow_const c).isPowPolylog

namespace IsPowPolylog






/-- If `g = Õ(n^a)` and `f = O(g)`, then `f = Õ(n^a)`. -/
theorem of_isBigO (hg : IsPowPolylog g a) (hfg : f =O[atTop] g) : IsPowPolylog f a := by
  obtain ⟨e, hg⟩ := hg
  exact ⟨e, hfg.trans hg⟩

/-- If `|f n| ≤ |g n|` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left (hg : IsPowPolylog g a) (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : IsPowPolylog f a :=
  hg.of_isBigO (IsBigO.of_bound' h)

/-- If `0 ≤ f n ≤ g n` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left_of_nonneg (hg : IsPowPolylog g a) (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : IsPowPolylog f a :=
  hg.mono_left ((h0.and h).mono fun _ hn => abs_le_abs_of_nonneg hn.1 hn.2)

/-- The exponent may be raised. -/
protected theorem mono (hf : IsPowPolylog f a) (hab : a ≤ b) : IsPowPolylog f b := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.trans (isBigO_rpow_mul_log_pow_of_le hab le_rfl)⟩

/-- `Õ(n^a) + Õ(n^a) = Õ(n^a)`. -/
protected theorem add (hf : IsPowPolylog f a) (hg : IsPowPolylog g a) :
    IsPowPolylog (fun n => f n + g n) a := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  exact ⟨max e₁ e₂, (hf.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_left _ _))).add
    (hg.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_right _ _)))⟩

/-- Constant factors are absorbed. -/
theorem const_mul (hf : IsPowPolylog f a) (c : ℝ) : IsPowPolylog (fun n => c * f n) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.const_mul_left c⟩





/-- `Õ(n^a) · Õ(n^b) = Õ(n^(a+b))`. -/
protected theorem mul (hf : IsPowPolylog f a) (hg : IsPowPolylog g b) :
    IsPowPolylog (fun n => f n * g n) (a + b) := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  refine ⟨e₁ + e₂, (hf.mul hg).congr' EventuallyEq.rfl ?_⟩
  filter_upwards [rpow_mul_rpow_eventuallyEq a b] with n hn
  rw [← hn, pow_add, mul_mul_mul_comm]

/-- `Õ(n^a) ^ k = Õ(n^(a k))` for a natural number `k`. -/
protected theorem pow (hf : IsPowPolylog f a) (k : ℕ) :
    IsPowPolylog (fun n => f n ^ k) (a * k) := by
  obtain ⟨e, hf⟩ := hf
  refine ⟨e * k, (hf.pow k).congr_right fun n => ?_⟩
  rw [mul_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul n.cast_nonneg]
























/-- If `f = Õ(n^a)` and `g n = f n` for all large `n`, then `g = Õ(n^a)`. -/
protected theorem congr (hf : IsPowPolylog f a) (h : f =ᶠ[atTop] g) : IsPowPolylog g a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.congr' h EventuallyEq.rfl⟩












end IsPowPolylog

theorem IsPowPolylog.isBigOPow (hf : IsPowPolylog f a) (hab : a < b) : IsBigOPow f b := by
  obtain ⟨e, hf⟩ := hf
  exact hf.trans (isBigO_rpow_mul_log_pow_rpow hab e)

/-- If `size n = O(n^μ)` for some `μ`, then `log (size n) = Õ(1)`. -/
theorem IsBigOPow.isPowPolylog_log_natCast {size : ℕ → ℕ} {μ : ℝ}
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) :
    IsPowPolylog (fun n => Real.log (size n)) 0 := by
  refine (isPowPolylog_log.const_mul (max μ 0 + 1)).mono_left_of_nonneg
    (Eventually.of_forall fun n => Real.log_natCast_nonneg _) ?_
  filter_upwards [(hsize.mono (le_max_left μ 0)).eventually_abs_le (lt_add_one _),
    eventually_gt_atTop 0] with n hle hn
  obtain hzero | hpos := (size n).eq_zero_or_pos
  · rw [hzero, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (add_nonneg (le_max_right μ 0) zero_le_one) (Real.log_natCast_nonneg n)
  · rw [abs_of_nonneg (Nat.cast_nonneg _)] at hle
    rw [← Real.log_rpow (Nat.cast_pos.2 hn)]
    exact Real.log_le_log (Nat.cast_pos.2 hpos) hle











/-- Substituting a size: if `G(s) = Õ(s^a)` and `size n = O(n^μ)` with `a, μ ≥ 0`, then
`G(size n) = Õ(n^(a μ))`. The sizes need not tend to infinity. -/
protected theorem IsPowPolylog.comp {G : ℕ → ℝ} {size : ℕ → ℕ} {μ : ℝ} (hG : IsPowPolylog G a)
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) :
    IsPowPolylog (fun n => G (size n)) (a * μ) := by
  obtain ⟨e, hG⟩ := hG
  have hmain := (hsize.rpow ha).isPowPolylog.mul (hsize.isPowPolylog_log_natCast.pow e)
  rw [zero_mul, add_zero, mul_comm μ a] at hmain
  exact (hmain.add ((isPowPolylog_const 1).mono (mul_nonneg ha hμ))).of_isBigO
    (isBigO_comp_add_one hG (fun s => mul_nonneg (Real.rpow_nonneg s.cast_nonneg a)
      (pow_nonneg (Real.log_natCast_nonneg s) e)) size)

/-- `n ^ a * (log n + 1) ^ e = Õ(n^a)`. -/
theorem isPowPolylog_rpow_mul_log_add_one_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * (Real.log n + 1) ^ e) a := by
  have h := (isPowPolylog_rpow a).mul ((isPowPolylog_log.add (isPowPolylog_const 1)).pow e)
  rwa [zero_mul, add_zero] at h

/-- `log (c * n ^ κ) = Õ(1)`. -/
theorem isPowPolylog_log_mul_rpow (c κ : ℝ) :
    IsPowPolylog (fun n : ℕ => Real.log (c * (n : ℝ) ^ κ)) 0 := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa only [zero_mul, Real.log_zero] using isPowPolylog_const 0
  · refine ((isPowPolylog_const (Real.log c)).add (isPowPolylog_log.const_mul κ)).congr ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [Real.log_mul hc (Real.rpow_pos_of_pos hpos κ).ne', Real.log_rpow hpos]

protected theorem IsBigOPow.comp {G : ℕ → ℝ} {size : ℕ → ℕ} {μ : ℝ}
    (hG : IsBigOPow G a) (hsize : IsBigOPow (fun n => (size n : ℝ)) μ)
    (ha : 0 ≤ a) (hμ : 0 ≤ μ) : IsBigOPow (fun n => G (size n)) (a * μ) := by
  have hmodel : IsBigOPow (fun n => (size n : ℝ) ^ a + 1) (a * μ) :=
    ((hsize.rpow ha).mono (mul_comm μ a).le).add
      ((isBigOPow_const 1).mono (mul_nonneg ha hμ))
  exact hmodel.of_isBigO
    (isBigO_comp_add_one hG (fun s => Real.rpow_nonneg s.cast_nonneg a) size)

end ThreeSumApsp

end
end


section
public section
namespace ThreeSumApsp

/-- `logU u ≥ log 2`. -/
theorem log_two_le_logU (u : ℝ) : Real.log 2 ≤ logU u :=
  Real.log_le_log two_pos (le_max_right _ _)

/-- `logU u > 0`. -/
theorem logU_pos (u : ℝ) : 0 < logU u :=
  (Real.log_pos one_lt_two).trans_le (log_two_le_logU u)

/-- `1 + logU u ≥ 1`. -/
theorem one_le_one_add_logU (u : ℝ) : 1 ≤ 1 + logU u :=
  le_add_of_nonneg_right (logU_pos u).le



/-- `logU` is nondecreasing. -/
theorem isPowPolylog_logU_of_le {mag : ℕ → ℝ} {c κ : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → 1 ≤ mag n ∧ mag n ≤ c * (n : ℝ) ^ κ) :
    IsPowPolylog (fun n => logU (mag n)) 0 := by
  refine (isPowPolylog_log_mul_rpow (2 * c) κ).mono_left_of_nonneg
    (.of_forall fun n => (logU_pos _).le) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨hone, hle⟩ := h n hn
  refine Real.log_le_log (lt_max_of_lt_right two_pos) (max_le ?_ ?_) <;> rw [mul_assoc] <;> linarith

end ThreeSumApsp
end
end

-- Original source module: ThreeSumApsp.Util.Asymptotics.PowLittleO
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Calculating with `n^{a+o(1)}`

`IsPowLittleO f a` reads `f(n) = n^{a+o(1)}` as an upper bound on `|f(n)|`: there is a sequence
`ε(n) → 0` with `|f(n)| ≤ n^{a+ε(n)}` for all large `n`. This says the same as `f(n) = O(n^{a+η})`
for every `η > 0` (`isPowLittleO_iff`). In the second form the rules of the notation follow from the
rules for `O`:

* the exponent may grow (`IsPowLittleO.mono`), and a strictly larger exponent absorbs the `o(1)`
  (`IsPowLittleO.isBigOPow`);
* sums, products and constant factors (`IsPowLittleO.add`, `IsPowLittleO.mul`,
  `IsPowLittleO.const_mul`);
* `(n^{d+o(1)})^{c+o(1)} = n^{cd+o(1)}` for `c, d ≥ 0` (`IsPowLittleO.comp`);
* `O(n^a)` and `O(n^a (log n)^{O(1)})` are `n^{a+o(1)}` (`IsBigOPow.isPowLittleO`,
  `IsPowPolylog.isPowLittleO`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}

/-! ### The two readings of the notation -/

/-- The `o(1)` is absorbed: if `f = n^{a+o(1)}` and `a < b`, then `|f n| ≤ n ^ b` for all large `n`.
-/
theorem IsPowLittleO.eventually_abs_le (h : IsPowLittleO f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by
  obtain ⟨ε, hε, hf⟩ := h
  filter_upwards [hf, hε.eventually_lt_const (sub_pos.2 hab), eventually_ge_atTop 1]
    with n hfn hεn hn
  exact hfn.trans (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) (by linarith))

/-- If for every `η > 0`, `|f(n)| ≤ n^{a+η}` for all large `n`, then `f(n) = n^{a+o(1)}`. For
`ε(n)` take the excess of the exponent that is needed at `n`: the number with
`n^{a+ε(n)} = max(|f(n)|, n^a)`. -/
theorem IsPowLittleO.of_eventually_abs_le
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ (a + η)) : IsPowLittleO f a := by
  -- All three claims are about `n ≥ 2`, where `n > 1` and the maximum is positive.
  have hbase : ∀ n : ℕ, 2 ≤ n → (1 : ℝ) < n ∧ 0 < max |f n| ((n : ℝ) ^ a) := fun n hn =>
    ⟨by exact_mod_cast hn, lt_max_of_lt_right (Real.rpow_pos_of_pos (by positivity) a)⟩
  refine ⟨fun n => Real.logb n (max |f n| ((n : ℝ) ^ a)) - a,
    tendsto_order.2 ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩, ?_⟩
  · -- `ε(n) ≥ 0`, because the maximum is at least `n^a`.
    filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    have hge : a ≤ Real.logb n (max |f n| ((n : ℝ) ^ a)) :=
      (Real.le_logb_iff_rpow_le hn1 hpos).2 (le_max_right _ _)
    linarith [hδ, hge]
  · -- `ε(n) ≤ δ/2` as soon as `|f(n)| ≤ n^{a+δ/2}`.
    filter_upwards [h (δ / 2) (half_pos hδ), eventually_ge_atTop 2] with n hfn hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    have hle : Real.logb n (max |f n| ((n : ℝ) ^ a)) ≤ a + δ / 2 :=
      (Real.logb_le_iff_le_rpow hn1 hpos).2
        (max_le hfn (Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)))
    linarith [hδ, hle]
  · -- `n^{a+ε(n)}` is the maximum.
    filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨hn1, hpos⟩ := hbase n hn
    rw [add_sub_cancel, Real.rpow_logb (zero_lt_one.trans hn1) hn1.ne' hpos]
    exact le_max_left _ _

/-- `f(n) = n^{a+o(1)}` if and only if `f(n) = O(n^{a+η})` for every `η > 0`. -/
theorem isPowLittleO_iff : IsPowLittleO f a ↔ ∀ η : ℝ, 0 < η → IsBigOPow f (a + η) :=
  ⟨fun h η hη => (isBigOPow_rpow (a + η)).mono_left
      ((h.eventually_abs_le (lt_add_of_pos_right a hη)).mono
        fun _ hfn => hfn.trans (le_abs_self _)),
    fun h => .of_eventually_abs_le fun η hη =>
      (h (η / 2) (half_pos hη)).eventually_abs_le (by linarith)⟩

/-! ### The rules -/

/-- `n^{a+o(1)} ⊆ n^{b+o(1)}` for `a ≤ b`. -/
protected theorem IsPowLittleO.mono (h : IsPowLittleO f a) (hab : a ≤ b) : IsPowLittleO f b :=
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 h η hη).mono (by linarith)

/-- `n^{a+o(1)} ⊆ O(n^b)` for `a < b`. -/
theorem IsPowLittleO.isBigOPow (h : IsPowLittleO f a) (hab : a < b) : IsBigOPow f b :=
  (isPowLittleO_iff.1 h (b - a) (sub_pos.2 hab)).mono (by linarith)

/-- `O(n^a) ⊆ n^{a+o(1)}`. -/
theorem IsBigOPow.isPowLittleO (h : IsBigOPow f a) : IsPowLittleO f a :=
  isPowLittleO_iff.2 fun _ hη => h.mono (by linarith)

/-- `O(n^a (log n)^{O(1)}) ⊆ n^{a+o(1)}`. -/
theorem IsPowPolylog.isPowLittleO (h : IsPowPolylog f a) : IsPowLittleO f a :=
  isPowLittleO_iff.2 fun _ hη => h.isBigOPow (by linarith)

/-- `n^{a+o(1)} + n^{a+o(1)} = n^{a+o(1)}`. -/
protected theorem IsPowLittleO.add (hf : IsPowLittleO f a) (hg : IsPowLittleO g a) :
    IsPowLittleO (fun n => f n + g n) a :=
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 hf η hη).add (isPowLittleO_iff.1 hg η hη)

/-- `n^{a+o(1)} · n^{b+o(1)} = n^{a+b+o(1)}`. -/
protected theorem IsPowLittleO.mul (hf : IsPowLittleO f a) (hg : IsPowLittleO g b) :
    IsPowLittleO (fun n => f n * g n) (a + b) :=
  isPowLittleO_iff.2 fun η hη => ((isPowLittleO_iff.1 hf _ (half_pos hη)).mul
    (isPowLittleO_iff.1 hg _ (half_pos hη))).mono (by linarith)

/-- Constant factors are absorbed. -/
theorem IsPowLittleO.const_mul (hf : IsPowLittleO f a) (c : ℝ) :
    IsPowLittleO (fun n => c * f n) a :=
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 hf η hη).const_mul_left c

/-! ### Composition -/

/-- For `c, d ≥ 0` and `η > 0` there is `t > 0` with `(c + t)(d + t) ≤ cd + η`. -/
private theorem exists_pos_add_mul_add_le (hc : 0 ≤ c) (hd : 0 ≤ d) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ (c + t) * (d + t) ≤ c * d + η := by
  have hcd : 0 < c + d + 1 := by linarith
  have ht : 0 < min 1 (η / (c + d + 1)) := lt_min one_pos (div_pos hη hcd)
  refine ⟨min 1 (η / (c + d + 1)), ht, ?_⟩
  set t := min 1 (η / (c + d + 1))
  have hsq : t * t ≤ t * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) ht.le
  have hlin : t * (c + d + 1) ≤ η := (le_div_iff₀ hcd).1 (min_le_right _ _)
  -- `(c + t)(d + t) = cd + t(c + d) + t² ≤ cd + t(c + d + 1) ≤ cd + η`
  linarith [hsq, hlin]

/-- `(n^{d+o(1)})^{c+o(1)} = n^{cd+o(1)}`: if `T(s) = s^{c+o(1)}` and `size(n) = n^{d+o(1)}` then
`T(size(n)) = n^{cd+o(1)}`, for `c, d ≥ 0`. The sizes need not tend to infinity. -/
protected theorem IsPowLittleO.comp (hT : IsPowLittleO T c)
    (hs : IsPowLittleO (fun n => (size n : ℝ)) d) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IsPowLittleO (fun n => T (size n)) (c * d) := by
  refine isPowLittleO_iff.2 fun η hη => ?_
  obtain ⟨t, ht, hexp⟩ := exists_pos_add_mul_add_le hc hd hη
  exact ((isPowLittleO_iff.1 hT t ht).comp (isPowLittleO_iff.1 hs t ht) (by linarith)
    (by linarith)).mono hexp

end ThreeSumApsp

end
end



-- Original source module: ThreeSumApsp.Util.Asymptotics.UpperBounds
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# One-sided bounds `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`

A running time is bounded from above only. `UpperBigOPow f a`, `UpperPowPolylog f a` and
`UpperPowLittleO f a` say that `f(n)` is eventually at most `C n^a`, at most `C n^a (log n)^e`, and
at most `n^{a+ε(n)}` with `ε(n) → 0`, where `IsBigOPow`, `IsPowPolylog` and `IsPowLittleO` say this
of `|f(n)|`.

A bound on `|f|` is a bound on `f` (`IsBigOPow.upperBigOPow`), and the function may be replaced by a
smaller one (`mono_left`); these two lemmas have the same names for the three classes. For `Õ(n^a)`
and `n^{a+o(1)}` a bound on `f` is a bound by a nonnegative function of the class that bounds `|f|`
(`UpperPowPolylog.exists_isPowPolylog`). For `Õ(n^a)` the closure properties follow: a bound on `f`
is a bound on `|f|` if `f` is eventually nonnegative (`UpperPowPolylog.isPowPolylog`), sums,
nonnegative constant factors, products with a nonnegative factor, a larger exponent (`mono`).
Logarithms and the `o(1)` are absorbed by a strictly larger exponent
(`UpperPowPolylog.upperBigOPow`, `UpperPowLittleO.upperBigOPow`).
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp





/-- There is a sequence `ε(n) → 0` with `f(n) ≤ n^{a+ε(n)}` for all large `n`: a bound on `f` and
not on `|f|` (that is `IsPowLittleO`). -/
def UpperPowLittleO (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ᶠ n : ℕ in Filter.atTop, f n ≤ (n : ℝ) ^ (a + ε n)

variable {f f' g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` from above -/

/-- `f = O(n^a)` is in particular an upper bound on `f`. -/
theorem IsBigOPow.upperBigOPow (hf : IsBigOPow f a) : UpperBigOPow f a := by
  obtain ⟨C, hC⟩ := IsBigO.bound hf
  refine ⟨C, hC.mono fun n hn => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)] at hn
  exact (le_abs_self _).trans hn

namespace UpperBigOPow

/-- The function may be replaced by one that is eventually at most as large. -/
theorem mono_left (h : UpperBigOPow f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) : UpperBigOPow f' a := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, (hle.and hC).mono fun n hn => hn.1.trans hn.2⟩

end UpperBigOPow

/-! ### `Õ(n^a)` from above -/



namespace UpperPowPolylog

















end UpperPowPolylog

/-! ### `n^{a+o(1)}` from above -/

/-- `f = n^{a+o(1)}` is in particular an upper bound on `f`. -/
theorem IsPowLittleO.upperPowLittleO (hf : IsPowLittleO f a) : UpperPowLittleO f a := by
  obtain ⟨ε, hε, hf⟩ := hf
  exact ⟨ε, hε, hf.mono fun n hn => (le_abs_self _).trans hn⟩

namespace UpperPowLittleO

/-- The function may be replaced by one that is eventually at most as large. -/
theorem mono_left (h : UpperPowLittleO f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) :
    UpperPowLittleO f' a := by
  obtain ⟨ε, hε, hf⟩ := h
  exact ⟨ε, hε, (hle.and hf).mono fun n hn => hn.1.trans hn.2⟩

/-- An upper bound `n^{a+o(1)}` is a bound by a nonnegative function of the class `n^{a+o(1)}`. -/
theorem exists_isPowLittleO (h : UpperPowLittleO f a) :
    ∃ g : ℕ → ℝ, (∀ n, 0 ≤ g n) ∧ IsPowLittleO g a ∧ ∀ᶠ n in atTop, f n ≤ g n := by
  obtain ⟨ε, hε, hf⟩ := h
  exact ⟨fun n => (n : ℝ) ^ (a + ε n), fun n => Real.rpow_nonneg n.cast_nonneg _,
    ⟨ε, hε, Eventually.of_forall fun n => (abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg _)).le⟩,
    hf⟩

/-- The `o(1)` is absorbed: `n^{a+o(1)} ⊆ O(n^b)` for `a < b`, from above. -/
theorem upperBigOPow (h : UpperPowLittleO f a) (hab : a < b) : UpperBigOPow f b := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowLittleO
  exact (hg.isBigOPow hab).upperBigOPow.mono_left hfg

end UpperPowLittleO

end ThreeSumApsp

end
end



namespace ThreeSumApsp

theorem Theorem21a.of_CH20_VW13 (M : DetTimeModel) (hCH : Claim.CH20_Theorem_5_1 M)
    (hVW : Claim.VW13_Theorem_4_3 M) : Claim.Theorem_21a M := by
  obtain ⟨c, E₂, Num₂, size₂, hc, hE₂, hNum₂, hsize₂, hsize₂_pos, hVW⟩ := hVW
  intro κ hκ
  obtain ⟨E₁, Num₁, mag₁, N, c', κ', hE₁, hNum₁, hN, hpos, hCH⟩ := hCH κ hκ
  have hN' := hN.isPowLittleO
  have hwords : IsPowLittleO (fun n : ℕ => 1 + logU (mag₁ n)) 0 :=
    ((isPowPolylog_const 1).add (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).isPowLittleO
  refine ⟨fun n => E₁ n + Num₁ n * (E₂ (N n) * (1 + logU (mag₁ n))), fun n => Num₁ n * Num₂ (N n),
    fun n => c * mag₁ n, fun n => size₂ (N n), c * c', κ', ?_, ?_, ?_, fun n hn => ?_,
    fun T hT => ?_⟩
  · -- the extra time: `Õ(n^{3/2}) + Õ(1) · N^{3/2+o(1)} · Õ(1)`
    exact hE₁.isPowLittleO.add ((hNum₁.isPowLittleO.mul
      ((hE₂.comp hN' (by norm_num) (by norm_num)).mul hwords)).mono (by norm_num))
  · -- the number of instances: `Õ(1) · O(N^{1/2})`
    exact (hNum₁.isPowLittleO.mul
      (hNum₂.isPowLittleO.comp hN' (by norm_num) (by norm_num))).mono (by norm_num)
  · -- their size: `O(N^{1/2})`
    exact (hsize₂.isPowLittleO.comp hN' (by norm_num) (by norm_num)).mono (by norm_num)
  · obtain ⟨hN1, hmag1, hmag⟩ := hpos n hn
    refine ⟨hsize₂_pos _ hN1, one_le_mul_of_one_le_of_one_le hc hmag1, ?_⟩
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmag (zero_le_one.trans hc)
  · obtain ⟨T', hT', hb⟩ := hCH _ (hVW T hT)
    exact ⟨T', hT', fun n hn => (hb n hn).trans (le_of_eq (by ring))⟩
theorem threeSum_of_uniform_theorem_21a (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21a M) :
    Claim.SolvedAlongPow M.threeSum UpperPowLittleO (2 - δ / 2) := by
  obtain ⟨K, -, hex⟩ := hu
  intro κ hκ
  obtain ⟨E, Num, mag, size, c', κ', hE, hNum, hsize, hpos, h⟩ := h21 κ hκ
  obtain ⟨T', hT', hb⟩ := h _ hex
  have hsizes := (isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).isPowLittleO.comp hsize
    (by linarith) (by norm_num)
  have hwords := (((isPowPolylog_const 1).add
    (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).pow 2).isPowLittleO
  have htotal : IsPowLittleO (fun n => E n + Num n * uniformTime K δ e (size n) (mag n))
      (2 - δ / 2) :=
    (hE.mono (by linarith)).add
      ((hNum.mul ((hsizes.mul hwords).const_mul K)).mono (le_of_eq (by push_cast; ring)))
  exact ⟨T', hT', htotal.upperPowLittleO.mono_left (Filter.eventually_atTop.2 ⟨1, hb⟩)⟩
theorem Claim.SolvedAlongPow.mono {S : (ℕ → ℝ → ℝ) → Prop} {Cls Cls' : (ℕ → ℝ) → ℝ → Prop}
    {a b : ℝ} (h : Claim.SolvedAlongPow S Cls a) (hCls : ∀ f, Cls f a → Cls' f b) :
    Claim.SolvedAlongPow S Cls' b := fun κ hκ =>
  let ⟨T, hT, hb⟩ := h κ hκ
  ⟨T, hT, hCls _ hb⟩

end ThreeSumApsp

namespace ThreeSumApsp.FromClaims

open ThreeSumApsp.WordRam
open EndStatement (Instr)

theorem solvedInTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ}
    (h : Claim.SolvedAlongPow S UpperBigOPow a) : SolvedInTime Q a 0 := by
  intro κ
  obtain ⟨T, hT, C, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact solvedAt_of_realized T κ (hR T hT) (C := C)
    (by simpa only [pow_zero, mul_one] using hb)

end ThreeSumApsp.FromClaims

open ThreeSumApsp ThreeSumApsp.WordRam in
/-- Uniform ExactTriangle time at exponent `3 - δ` yields the stated 3SUM exponent. -/
theorem solution (δ : ℝ) (r : ℚ) (e : ℕ) (hδ : δ ≤ 1)
    (hr : 2 - δ / 2 < (r : ℝ))
    (hu : ThreeSumApsp.Claim.ExactTriangleUniform Light.lightModel δ e) :
    EndStatement.ThreeSum.SolvedInTime r := by
  have h21 : ThreeSumApsp.Claim.Theorem_21a Light.lightModel :=
    ThreeSumApsp.Theorem21a.of_CH20_VW13 _ Light.Sec3.ChanHe.claim_CH20_Theorem_5_1
      Light.Sec3.claim_VW13_Theorem_4_3
  have h3 : ThreeSumApsp.WordRam.SolvedInTime EndStatement.ThreeSum (r : ℝ) 0 :=
    ThreeSumApsp.FromClaims.solvedInTime_of_claim Light.Sec3.realized_threeSum
      ((ThreeSumApsp.threeSum_of_uniform_theorem_21a _ e hδ hu h21).mono
        fun _ hf => hf.upperBigOPow hr)
  have hr0R : 0 ≤ (r : ℝ) := by linarith [hδ, hr]
  have hr0 : 0 ≤ r := by exact_mod_cast hr0R
  exact h3.endStatement rfl hr0

#print axioms solution
