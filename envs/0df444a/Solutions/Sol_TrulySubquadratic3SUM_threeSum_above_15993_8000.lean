-- Prove2me | solution 1 for TrulySubquadratic3SUM.threeSum_above_15993_8000
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T18:12:33.862881+00:00
-- url     : https://prove2.me/submissions/ae4e9f45-9b94-4655-b998-ab90ca3c8b37

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Corollary15_16
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_ThreeSumSource_ReductionClaims
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib
import Theorems.Thm_Light_Sec3_ChanHe_claim_CH20_Theorem_5_1
import Theorems.Thm_Light_Sec3_claim_VW13_Theorem_3_3
import Theorems.Thm_Light_Sec3_claim_VW13_Theorem_4_3
import Theorems.Thm_Light_Sec3_claim_VW18_Theorem_4_2
import Theorems.Thm_Light_Sec3_claim_apspFromMinPlus
import Theorems.Thm_Light_Sec3_claim_exactTriangleUniform_usingCorollary26
import Theorems.Thm_Light_Sec3_et17_spec
import Theorems.Thm_Light_Sec3_obeysBound17_hostTime
import Theorems.Thm_Light_Sec3_realized_threeSum
import Theorems.Thm_Light_Sec4_allInstances26_solves
import Theorems.Thm_Light_Sec4_allInstancesTime26_le
import Theorems.Thm_Light_Sec4_pre31_program31
import Theorems.Thm_Light_Sec4_queryAt_spec
import Theorems.Thm_Light_Sec4_specs40
import Theorems.Thm_Light_Wrap_realized
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_Theorem19_Choice_ceil_le_sqrt
import Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow
import Theorems.Thm_ThreeSumApsp_goodTime_uniformTime
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport

import Theorems.Thm_ThreeSumApsp_WordRam_SolvedInTime_endStatement

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


-- Original source module: StagedAPSPAccepted
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/



set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

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


/-!
# Powers of `n` and of `log n` for large `n`

The facts behind the paper's `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`, for functions of a natural number
`n` and in the language of Mathlib's `f =O[atTop] g`. Powers of `n` are monotone in the exponent
(`isBigO_rpow_rpow_of_le`, `isBigO_rpow_mul_log_pow_of_le`) and multiply by adding exponents
(`rpow_mul_rpow_eventuallyEq`). A constant or a power of `log n` is below every positive power of
`n` (`eventually_le_rpow`, `isLittleO_log_pow_rpow`). Hence `n ^ a * (log n) ^ e` is `o(n ^ b)` and
`O(n ^ b)` for `a < b` (`isLittleO_rpow_mul_log_pow_rpow`, `isBigO_rpow_mul_log_pow_rpow`), which is
where logarithms are absorbed for large `n`; with the constant absorbed too, this is
`eventually_mul_rpow_mul_log_pow_le`. The rounded power `⌈n ^ μ⌉` tends to infinity for `μ > 0`
(`tendsto_ceil_rpow_atTop`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

/-- A bound `|f n| ≤ C * g n` from some `n₀` on gives `f = O(g)`. -/
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

end ThreeSumApsp

end
end

section


/-!
# The notions of solving are monotone

That the program `P` with slope `b` solves the problem on the instances in `dom` within time `T`, at
every admissible word size, stays true for a larger slope, a smaller set of instances and a larger
time bound (`Solves.mono`).  The same holds for a two-stage data structure (`IsDataStructure.mono`).

* The item statements on the problems of the end statement use `SolvesWithin`.  It is `Solves` for
  the problem `ofEnd Q`, whose instances carry their size and a bound on their numbers
  (`solvesWithin_iff`, `solvedInTimeAt_iff`).

* A statement "there are a program and a constant `C` such that the time is at most `C f(x)`" stays
  true for every bound `g` with `f = O(g)`: `exists_solves_of_dominated`, and
  `exists_isDataStructure_of_dominated` for a data structure.
* For the bounds `O(n^a (log n)^e)` in one size: a larger exponent (`SolvedInTime.mono_exponent`),
  and a larger exponent that absorbs the logarithms (`SolvedInPolylogTime.solvedInTime`).
-/

public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)
open Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/




























/-- `EndStatement.Problem.SolvedBy` counts the output cells as `1 + len + i`, and `output` counts
them as `(len + 1) + i`. -/
theorem output_cons {W : ℕ} (c : ℤ → BitVec W) (n : ℤ) (l : List ℤ) :
    (fun i : ℕ => (c ((1 + l.length + i : ℕ) : ℤ)).toInt) = output c (n :: l).length := by
  funext i
  simp only [output, List.length_cons, Nat.add_comm 1]
  rfl

/-- `SolvesWithin` is `Solves` for the problem `ofEnd Q`, on the instances with `U = n^κ`. -/
theorem solvesWithin_iff {Q : EndStatement.Problem} {κ : ℕ} {P : List Instr} {b : ℕ} {T : ℕ → ℝ} :
    SolvesWithin Q κ P b T ↔ Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ) fun x => T x.n := by
  constructor
  · intro h x hx bits hbits
    obtain ⟨t, ht, verdict, m, hexec, hyes, hout⟩ :=
      h x.n x.x (hx ▸ x.bounded) bits (by simpa [Admissible] using hbits)
    exact ⟨t, verdict, m, ht, hexec, hyes, output_cons m x.n (Q.input x.x) ▸ hout⟩
  · intro h n x hx W hW
    obtain ⟨t, verdict, c, ht, hrun, hyes, hout⟩ :=
      h ⟨n, n ^ κ, x, hx⟩ rfl W (by simpa [Admissible] using hW)
    exact ⟨t, ht, verdict, c, hrun, hyes, (output_cons c n (Q.input x)).symm ▸ hout⟩

/-- `SolvedInTimeAt` in terms of `Solves`. -/
theorem solvedInTimeAt_iff {Q : EndStatement.Problem} {κ : ℕ} {a : ℝ} {e : ℕ} :
    SolvedInTimeAt Q κ a e ↔ ∃ (P : List Instr) (b : ℕ) (C : ℝ),
      Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ)
        fun x => C * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1) := by
  simp only [SolvedInTimeAt, solvesWithin_iff]

/-! ## Monotonicity -/

/-- `Solves` stays true for a larger slope, a smaller set of instances and a larger time bound. -/
theorem Solves.mono {prob : Problem} {P : List Instr} {b b' : ℕ} {dom dom' : prob.Inst → Prop}
    {T T' : prob.Inst → ℝ} (h : _root_.ThreeSumApsp.WordRam.Solves prob P b dom T) (hb : b ≤ b') (hdom : ∀ x, dom' x → dom x)
    (hT : ∀ x, dom' x → T x ≤ T' x) : _root_.ThreeSumApsp.WordRam.Solves prob P b' dom' T' := by
  intro x hx bits hadm
  obtain ⟨t, verdict, c, ht, he, ha⟩ :=
    h x (hdom x hx) bits (le_trans (Nat.mul_le_mul_right _ hb) hadm)
  exact ⟨t, verdict, c, ht.trans (hT x hx), he, ha⟩



















/-! ## Bounds up to a constant -/

/-- A program that solves a problem in time `O(f)` solves it in time `O(f')` if `f = O(f')`. -/
theorem exists_solves_of_dominated {prob : Problem} {dom dom' : prob.Inst → Prop}
    {f f' : prob.Inst → ℝ}
    (h : ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom fun x => C * f x)
    (hdom : ∀ x, dom' x → dom x) (hf : Dominated dom' f f')
    (hf0 : ∀ x, dom' x → 0 ≤ f x := by intro _ _; positivity) :
    ∃ (P : List Instr) (b : ℕ) (C : ℝ), Solves prob P b dom' fun x => C * f' x := by
  obtain ⟨P, b, C, h⟩ := h
  obtain ⟨K, -, hf⟩ := hf.const_mul_of_nonneg C hf0
  exact ⟨P, b, K, h.mono le_rfl hdom hf⟩






















/-! ## Bounds in one size -/

/-- The bound `O(n^a (log n)^e)` may be replaced by a bound `O(n^a' (log n)^e')` that is at least as
large, up to a constant, for all large `n`. -/
theorem SolvedInTimeAt.of_eventually_le {Q : EndStatement.Problem} {κ : ℕ} {a a' C : ℝ} {e e' : ℕ}
    (h : SolvedInTimeAt Q κ a e)
    (hle : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ a * Real.log n ^ e ≤ C * ((n : ℝ) ^ a' * Real.log n ^ e')) :
    SolvedInTimeAt Q κ a' e' := by
  have hall : Dominated (fun _ : ℕ => True) (fun n => (n : ℝ) ^ a * Real.log n ^ e + 1)
      fun n => (n : ℝ) ^ a' * Real.log n ^ e' + 1 :=
    (Dominated.of_eventually_add_one hle fun n => by positivity).add
      (.of_le fun n _ => le_add_of_nonneg_left (by positivity))
  exact solvedInTimeAt_iff.2 (exists_solves_of_dominated (solvedInTimeAt_iff.1 h) (fun _ hx => hx)
    (hall.comp (fun x : Bounded Q => x.n) fun _ _ => trivial))













/-- A bound `O(n^a (log n)^{O(1)})` is a bound `O(n^a')` for `a < a'`. -/
theorem SolvedInPolylogTime.solvedInTime {Q : EndStatement.Problem} {a a' : ℝ}
    (h : SolvedInPolylogTime Q a) (ha : a < a') : SolvedInTime Q a' 0 := fun κ =>
  let ⟨e, he⟩ := h κ
  he.of_eventually_le (C := 1) <| by
    simpa only [one_mul, pow_zero, mul_one] using eventually_mul_rpow_mul_log_pow_le 1 ha e

end ThreeSumApsp.WordRam

end
end

section


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/













/-! ## The rules -/





































































/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/







/-- The sum of two expressions. -/
infixl:65 " +' " => Expr.op Op.add
/-- The difference of two expressions. -/
infixl:65 " -' " => Expr.op Op.sub
/-- The product of two expressions. -/
infixl:70 " *' " => Expr.op Op.mul
@[inherit_doc] infix:50 " <' " => Cond.lt
@[inherit_doc] infix:50 " =' " => Cond.eq
@[inherit_doc] infixr:30 " ;; " => Stmt.seq



@[inherit_doc] infix:50 " ≤' " => Cond.le








/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame














/-! ## The limits -/
























end Light

end
end

section


/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}















/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}


























/-! ## The tactics -/









































end Light

end
end

section


/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/







/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/

































/-! ## The next index -/























end Nat

namespace Int

/-! ## Residues as natural numbers -/










end Int

end
end

section


/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/

























































/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/












































































/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/
















/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end
end

section


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}























































































































































end Light

end
end

section


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/




































/-! ## The default proofs -/



































/-! ## Rules for blocks -/



























/-! ## Sequencing: what is left of the time goes to the rest of the program -/
















































































/-! ## Loops whose body is a block -/



/-! ## Counting loops -/









end Light

end
end

section


/-!
# Arrays in the memory

A routine assumes the same facts about each of its arrays: which list it holds, how long the list
is, and that it lies below some address `top`, from which on the routine writes: the free pointer,
the place of the result, the scratch space.  `ListAt μ a l N top` is the record of these three
facts, and `ArrayAt μ a l N U top` adds a bound `U` on the entries.  `IndexAt μ a l N p top` is the
record for a list of natural numbers below `p`.  What a routine assumes is then a record with one
field for each array.

* `ListAt.keep`, `ArrayAt.keep`: an array stays in place when its cells do not change.
* `ListAt.mono`, `ArrayAt.mono`: `top` and `U` may grow.
* `ListAt.read`, `ArrayAt.read`, `ArrayAt.abs_read_le`: what a cell holds, and how large it is.
* `ListAt.drop_take`, `ArrayAt.drop_take`: a piece of an array is an array.
* `IndexAt.keep`, `IndexAt.read`, `IndexAt.getD_lt`: the same for natural numbers.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}















namespace ListAt




















end ListAt

namespace ArrayAt



























end ArrayAt









namespace IndexAt

variable {l : List ℕ} {p : ℕ}






















end IndexAt

end Light

end
end

section


/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/















/-! ## The value of an expression -/





/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}

























































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end
end

section


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}





















end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

















end

end Light

end
end

section


/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam
















































































end Light

end
end

section


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/

























/-! ## Specifications of single routines -/






/-! ## Tasks and solvers -/




















































/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/
































end Light

end
end

section


/-!
# The answer of a decision problem as a number

A routine for a decision problem returns 1 for yes and 0 for no: `flag p` is this number for the
proposition `p`.
-/

@[expose] public section

namespace ThreeSumApsp

























end ThreeSumApsp

end
end

section


/-!
# Ceilings of quotients and logarithms, floors and ceilings of roots

General facts about natural and real numbers. The quotient of two natural numbers, rounded up, is
Mathlib's `a ⌈/⌉ b`. It is computed by `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`.
It is the ceiling of the real quotient (`Nat.ceil_div_eq_ceilDiv`) and the least `k` with
`a ≤ k * b` (`Nat.ceilDiv_le_iff`, `Nat.lt_ceilDiv_iff`), so `a ≤ a ⌈/⌉ b * b < a + b`
(`Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`). The power of `b` with exponent `⌈log_b n⌉` is at most
`b * n` (`Nat.pow_clog_le_mul`). A natural number is compared with an `e`-th root by its `e`-th
power (`Real.natCast_le_rpow_inv_iff`, `Real.rpow_inv_le_natCast_iff`). `cbrtCeil n` is the cube
root of `n`, rounded up.
-/

public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/






























/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/



end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/





end Real

namespace ThreeSumApsp




end ThreeSumApsp

end
end

section


/-!
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/

@[expose] public section

namespace Real

/-! ### Values -/

/-- `1 / 2 < log 2`. -/
theorem one_half_lt_log_two : 1 / 2 < log 2 :=
  lt_trans (by norm_num) log_two_gt_d9

/-- `log 2 < 1`. -/
theorem log_two_lt_one : log 2 < 1 :=
  log_two_lt_d9.trans (by norm_num)





















/-- `1 / 2 ≤ log x` for `x ≥ 2`. -/
theorem one_half_le_log_of_two_le {x : ℝ} (hx : 2 ≤ x) : 1 / 2 ≤ log x :=
  one_half_lt_log_two.le.trans (log_le_log two_pos hx)







/-! ### The rounded logarithm `Nat.clog` -/

/-- `⌈log_b n⌉ < log_b n + 1`, for all natural numbers `b` and `n` (for `b ≤ 1` or `n = 0` both
logarithms are `0`). -/
theorem natCast_clog_lt_logb_add_one (b n : ℕ) : (Nat.clog b n : ℝ) < logb b n + 1 := by
  rw [← natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (div_nonneg (log_natCast_nonneg n) (log_natCast_nonneg b))














end Real

namespace ThreeSumApsp






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

end ThreeSumApsp

end
end

section


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















variable {f f' g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` from above -/








namespace UpperBigOPow






end UpperBigOPow

/-! ### `Õ(n^a)` from above -/

/-- `f = Õ(n^a)` is in particular an upper bound on `f`. -/
theorem IsPowPolylog.upperPowPolylog (hf : IsPowPolylog f a) : UpperPowPolylog f a := by
  obtain ⟨e, hf⟩ := hf
  obtain ⟨C, hC⟩ := hf.bound
  refine ⟨C, e, hC.mono fun n hn => ?_⟩
  have hnonneg : 0 ≤ (n : ℝ) ^ a * Real.log n ^ e :=
    mul_nonneg (Real.rpow_nonneg n.cast_nonneg a) (pow_nonneg (Real.log_natCast_nonneg n) e)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
  exact (le_abs_self _).trans hn

namespace UpperPowPolylog

/-- The function may be replaced by one that is eventually at most as large. -/
theorem mono_left (h : UpperPowPolylog f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) :
    UpperPowPolylog f' a := by
  obtain ⟨C, e, hC⟩ := h
  exact ⟨C, e, (hle.and hC).mono fun n hn => hn.1.trans hn.2⟩
















































end UpperPowPolylog

/-! ### `n^{a+o(1)}` from above -/






namespace UpperPowLittleO




















end UpperPowLittleO

end ThreeSumApsp

end
end

section


/-!
# Orders of growth of counts

The time and the need of a program are natural numbers, given by explicit expressions in the
parameters of the input.  Only their order of growth is needed.  This file has one calculus
that reads the order of growth off such an expression, so that no constant is ever written out.

A *scale* (`Scale α ι`) fixes the parameters `x : α` for which bounds are claimed (`dom`) and some
quantities that are at least 1 there: the *bases* `base i`, whose powers are counted, and one more,
`hidden`, whose powers are not.  `s.SoftO t e` says that the count `t` is at most a constant times a
power of `hidden` times the monomial `∏ i, base i ^ e i`.  Three examples:

* bases `n`, `√D`, `κ log n` and `hidden = 1`: `s.SoftO t ![2, 1, 1]` is `t = O(n² √D κ log n)`;
* one base `√n` and `hidden = log n`: `s.SoftO t ![3]` is `t = Õ(n^{3/2})`;
* no base and `hidden = n U`: `s.SoftO t ![]` says that `t` is polynomially bounded.

So `SoftO` is `O` up to powers of `hidden`: it is `O` itself if `hidden = 1`, and `Õ` if `hidden` is
a logarithm.  The bounds hold on the whole domain and not only from some point on.

The exponents follow the expression.  A constant has the exponents 0 (`SoftO.const`), a sum the
larger ones (`SoftO.add`), a product their sum (`SoftO.mul`), a power their multiple (`SoftO.pow`).
Exponents may be raised (`SoftO.mono`), and the count may be replaced by a smaller one
(`SoftO.of_le`, `SoftO.of_forall_le`).  If every base is at most `2 ^ hidden`, the binary logarithm
of a bounded count has the exponents 0 (`SoftO.log2`).

The tactic `growth [h₁, h₂, …]` applies these rules from the outside to the inside of the
expression.  The facts `hᵢ` bound the quantities at which the rules stop: parameters, and functions
whose bound is a lemma of its own.  A function that is to be followed into its definition is
unfolded first.

A bound leaves the calculus by `SoftO.exists_le`, or as a `Dominated` statement by
`SoftO.dominated`.
-/

@[expose] public section

namespace ThreeSumApsp














namespace Scale










variable {α ι : Type*} [Fintype ι] (s : Scale α ι)

















variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}







namespace SoftO

variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}

/-! ### Entering and leaving -/













/-! ### The rules -/








































































end SoftO

end Scale








































end ThreeSumApsp

end
end

section


/-!
# Polynomially bounded needs

The need of a program is given by explicit expressions in the size n of the input and the bound U on
its numbers.  `PolyBounded F` says that F(n, U) is at most a polynomial in (n + 1)(U + 1).  It is
the calculus `ThreeSumApsp.Scale.SoftO` on the scale `polyScale`, and the tactic `growth_poly`
proves it by following the expression.

Three such functions make a polynomially bounded need (`PolyBounded.polyNeed`), and the need of a
solver that a host calls has three such parts (`PolyNeed.word`, `PolyNeed.cells`, `PolyNeed.depth`).
So the need of a host is polynomially bounded if the need of its solver is; the tactic `poly_need`
proves this from the definition of the need of the host.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Upper bounds that are polynomial in (n + 1)(U + 1) -/













namespace PolyBounded

variable {F : ℕ → ℕ → ℕ}









end PolyBounded






namespace PolyBounded





end PolyBounded

/-! ## The need of a solver that a host calls

A polynomially bounded need, at a size `A(n, U)` and a bound `B(n, U)` that are polynomially
bounded, has polynomially bounded parts. -/

namespace PolyNeed

variable {need : ℕ → ℕ → Need} {A B : ℕ × ℕ → ℕ} {a b : Fin 0 → ℕ}









end PolyNeed








end Light

end
end

section


/-!
# The arithmetic behind the running-time claims of Section 3

Elementary inequalities that the deductions between running-time claims use silently.

* `⌈n^{1/3}⌉ ≥ 1` and `(log s + 1)^e ≥ 1`.
* Thin instances, `n ≥ D^18` (Theorem 5, Corollaries 15, 16 and 26): the overheads `n D`, `n² / √D`
  and `1` are at most `n² / D^a`, and so at most the bounds `n² log² D / D^{1/18}` and
  `n² / D^{0.063}`.
* The pieces into which Corollary 15 splits `W` have at most `n² / √D` query pairs (`splitCap_le`).
-/

public section

namespace ThreeSumApsp

/-! ## Two quantities that are at least 1 -/

/-- `⌈n^{1/3}⌉ ≥ 1` for `n ≥ 1`. -/
theorem one_le_cbrtCeil {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cbrtCeil n :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) _)



/-! ## Thin instances: `n ≥ D^18` -/








































/-! ## The pieces of Corollary 15 -/





























end ThreeSumApsp

end
end

section


/-!
# Logarithms up to a constant factor

Bounds on logarithms in the calculus `Dominated`, for every argument of a domain and not only for
large ones.

* Absorbing logarithms, for `x ≥ 1`: `(log x + 1) ^ e` is `O(x ^ η)` for `η > 0`
  (`dominated_log_add_one_pow_rpow`), hence `x ^ a * (log x) ^ e = O(x ^ b)` for `a < b`
  (`dominated_rpow_mul_log_pow_rpow`).
* From 2 on: `log x + 1 = O(log x)` (`dominated_log_add_one_log`) and `⌈log_b n⌉ + 1 = O(log n)`
  (`dominated_clog_add_one_log`).

For a natural number or a field of a parameter record in place of `x`, use `Dominated.comp`.
-/

public section

namespace ThreeSumApsp

open Real

/-! ### Absorbing logarithms, for all `x ≥ 1` -/




































/-! ### `log x + 1` and `⌈log_b n⌉ + 1` are `O(log)`, from `2` on -/

/-- `log x + 1 = O(log x)` on `x ≥ 2`. -/
theorem dominated_log_add_one_log :
    Dominated (fun x : ℝ => 2 ≤ x) (fun x => log x + 1) fun x => log x :=
  .of_le_const_mul (C := 3) (by norm_num) fun _ hx => by
    linarith [one_half_le_log_of_two_le hx]

/-- `⌈log_b n⌉ + 1 = O(log n)` on `n ≥ 2`, for every natural number `b`. -/
theorem dominated_clog_add_one_log (b : ℕ) :
    Dominated (fun n : ℕ => 2 ≤ n) (fun n => (Nat.clog b n : ℝ) + 1) fun n => log n := by
  have hlogb : 0 ≤ log b := log_natCast_nonneg b
  refine .of_le_const_mul (C := 1 / log b + 4) (by positivity) fun n hn => ?_
  have hhalf : 1 / 2 ≤ log n := one_half_le_log_of_two_le (by exact_mod_cast hn)
  have hclog := natCast_clog_lt_logb_add_one b n
  rw [add_mul, one_div_mul_eq_div]
  -- `⌈log_b n⌉ + 1 < log n / log b + 2` and `2 ≤ 4 log n`
  rw [logb] at hclog
  linarith [hclog, hhalf]

end ThreeSumApsp

end
end

section


/-!
# `logU`, the paper's `log U`

`logU u` is `log u`, read as `log 2` for `u < 2`.

* It is positive and nondecreasing, and `log (cu) ≤ log c + log u` for `c ≥ 1`.
* `log (cU) = O(log U)` (`dominated_logU_mul`) and `log (c n^κ) = O(log n)`
  (`dominated_logU_mul_rpow`).
* Along bounds `u(n) ≤ c n^κ` it is `Õ(1)` (`isPowPolylog_logU_of_le`).
-/

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
theorem logU_mono {u v : ℝ} (h : u ≤ v) : logU u ≤ logU v :=
  Real.log_le_log (lt_max_of_lt_right two_pos) (max_le_max_right _ h)

/-- `logU (c u) ≤ log c + logU u` for `c ≥ 1`. -/
theorem logU_mul_le {c : ℝ} (hc : 1 ≤ c) (u : ℝ) : logU (c * u) ≤ Real.log c + logU u := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hmax : (0 : ℝ) < max u 2 := lt_max_of_lt_right two_pos
  rw [logU, logU, ← Real.log_mul hc0.ne' hmax.ne']
  exact Real.log_le_log (lt_max_of_lt_right two_pos) (max_le
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hc0.le)
    ((le_max_right u 2).trans (le_mul_of_one_le_left hmax.le hc)))

/-- `logU u ≤ logU (c u)` for `c ≥ 1`, also for negative `u`. -/
theorem logU_le_logU_mul {c : ℝ} (hc : 1 ≤ c) (u : ℝ) : logU u ≤ logU (c * u) := by
  rcases le_or_gt 0 u with hu | hu
  · exact logU_mono (le_mul_of_one_le_left hu hc)
  · have hcu : c * u < 0 := mul_neg_of_pos_of_neg (zero_lt_one.trans_le hc) hu
    rw [logU, logU, max_eq_right (by linarith), max_eq_right (by linarith)]

/-- `logU (n^κ) ≤ log 2 + κ log n` for `n ≥ 1` and `κ ≥ 0`. -/
theorem logU_rpow_le {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    logU ((n : ℝ) ^ κ) ≤ Real.log 2 + κ * Real.log n := by
  have hpow : 1 ≤ (n : ℝ) ^ κ := Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ
  rw [← Real.log_rpow (Nat.cast_pos.2 hn), ← Real.log_mul two_ne_zero (by positivity)]
  exact Real.log_le_log (lt_max_of_lt_right two_pos) (max_le (by linarith) (by linarith))

/-! ## `logU` of a multiple -/

/-- `log (cU) = O(log U)` for a constant `c ≥ 1`. -/
theorem dominated_logU_mul {c : ℝ} (hc : 1 ≤ c) :
    Dominated (fun _ : ℝ => True) (fun U => logU (c * U)) logU := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  refine .of_le_const_mul (C := 1 + Real.log c / Real.log 2) (by positivity) fun U _ => ?_
  have hscale : Real.log c ≤ Real.log c / Real.log 2 * logU U := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left (log_two_le_logU U) hlogc
  linarith [logU_mul_le hc U, hscale]

/-- `log (c n^κ) = O(log n)` on `n ≥ 2`. -/
theorem dominated_logU_mul_rpow {c κ : ℝ} (hc : 1 ≤ c) (hκ : 0 ≤ κ) :
    Dominated (fun n : ℕ => 2 ≤ n) (fun n => logU (c * (n : ℝ) ^ κ)) fun n => Real.log n := by
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlog : Dominated (fun n : ℕ => 2 ≤ n) (fun n => Real.log n + 1) fun n => Real.log n :=
    dominated_log_add_one_log.comp (fun n : ℕ => (n : ℝ)) fun _ h => by exact_mod_cast h
  refine (hlog.const_mul (c := Real.log c + 1 + κ) (by positivity)).mono_left fun n hn => ?_
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  -- `log (c n^κ) ≤ log c + log 2 + κ log n ≤ (log c + 1 + κ) (log n + 1)`
  nlinarith [logU_mul_le hc ((n : ℝ) ^ κ), logU_rpow_le (one_le_two.trans hn) hκ,
    Real.log_two_lt_one, mul_nonneg hlogc hlogn]

/-! ## `logU` along bounds that are polynomial in `n` -/

/-- `log u(n) = Õ(1)` for bounds `1 ≤ u(n) ≤ c n^κ` on the numbers. -/
theorem isPowPolylog_logU_of_le {mag : ℕ → ℝ} {c κ : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → 1 ≤ mag n ∧ mag n ≤ c * (n : ℝ) ^ κ) :
    IsPowPolylog (fun n => logU (mag n)) 0 := by
  refine (isPowPolylog_log_mul_rpow (2 * c) κ).mono_left_of_nonneg
    (.of_forall fun n => (logU_pos _).le) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨hone, hle⟩ := h n hn
  refine Real.log_le_log (lt_max_of_lt_right two_pos) (max_le ?_ ?_) <;> rw [mul_assoc] <;> linarith

/-- `log (c n^κ) = Õ(1)`. -/
theorem isPowPolylog_logU_mul_rpow {c κ : ℝ} (hc : 1 ≤ c) (hκ : 0 ≤ κ) :
    IsPowPolylog (fun n : ℕ => logU (c * (n : ℝ) ^ κ)) 0 :=
  isPowPolylog_logU_of_le fun _ hn =>
    ⟨one_le_mul_of_one_le_of_one_le hc (Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ), le_rfl⟩

end ThreeSumApsp

end
end

section


/-!
# The steps and the scratch space of Strassen's recursion

At level j the operands are 2^j × 2^j matrices whose entries are vectors of p numbers, so that an
operand has 4^j · p numbers.  strScr p j ≤ 4^j · p (`strScr_le`), and both strScr and strSteps are
monotone in p.
-/

public section

namespace Light.Sec3




























end Light.Sec3

end
end

section


/-!
# The parameters of Theorems 17 and 19 in integer arithmetic

The proof of Theorem 19 chooses `D` and `g` as rounded real powers of `n`: "Let D be the largest
power of four with D ≤ n^{1/18}, […] and let g := ⌈D^{1/36}⌉" on the route through Theorem 5, and
"Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉" on the route through Corollary 26.  The reduction of
Theorem 17 cuts each residue class into chunks of at most `n²/√D` query pairs and splits `C` into
pieces of at most `⌈s/g⌉` vertices, where `s = ⌊√D⌋`.  A program finds all these numbers by
operations on natural numbers.

* `rootFloor e t` is `⌊t^{1/e}⌋` and `rootCeil e t` is `⌈t^{1/e}⌉` (`floor_rpow_inv`,
  `ceil_rpow_inv`); they are characterised by `x ≤ rootFloor e t ↔ x^e ≤ t` (`le_rootFloor_iff`) and
  `rootCeil e t ≤ g ↔ t ≤ g^e` (`rootCeil_le_iff`).
* The four functions `paramD₅Nat`, `paramG₅Nat`, `paramD₂₆Nat`, `paramG₂₆Nat` are the parameters
  of the proof of Theorem 19 (`paramD₅Nat_eq`, `paramG₅Nat_eq`, `paramD₂₆Nat_eq`, `paramG₂₆Nat_eq`);
  they are at least 1 and at most `n` or `D` (`paramD₂₆Nat_le`, `paramG₅Nat_le`, `paramG₂₆Nat_le`).
* The sizes of the proof of Theorem 17: `⌊n²/√D⌋ = ⌊√(n⁴/D)⌋` (`queryCapNat_eq`), `s` is the integer
  square root (`sOf_eq_sqrt`), and the rounded quotients are `a ⌈/⌉ b` (`pieceSizeNat_eq`,
  `numPiecesNat_eq`, `numChunks_eq`).  The middle part `C_k × ℤ_p` of an instance has at most `D`
  vertices (`pieceSize_mul_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Roots, rounded down and up -/























/-! ## The parameters of the proof of Theorem 19 -/
































































/-! ## The sizes of the instances of the proof of Theorem 17 -/







































































end ThreeSumApsp.Spec

end
end

section


/-!
# Scanning a piece (the proof of Theorem 17)

"For every query pair that the oracle accepts, scan the piece C_k of its instance for a c with
S(a,b,c) = 0".  The procedure scan (`scanBody`) goes through an interval of vertices `c` for a fixed
pair `(a, b)` (`scan_spec`, `scan_meets`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}






/-! ## The three arrays of weights -/










/-! ## Scanning an interval of vertices -/

namespace Scan


















end Scan





























end Light.Sec3

end
end

section


/-!
# The parameters of Theorems 17 and 19, without division and without roots

The proof of Theorem 19 chooses D as "the largest power of four with D ≤ n^{1/18}"
and g := ⌈D^{1/36}⌉, or D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉; the reduction of Theorem 17 uses
⌊n²/√D⌋ and quotients rounded up.  The language has neither division nor roots, so all of these are
found by counting up.  A power is compared with a bound without forming a number above the bound
times the base.

* powLt(g, e, t), for g ≥ 1, returns 1 if g^e < t, and 0 if not (`powLt_meets`); what it holds after
  i factors is `capPow g t i`.
* rootCeil(e, t) returns the least g with g^e ≥ t (`rootCeil_meets`).
* The four parameters; 5 and 26 stand for the two routes of Theorem 19, through Theorem 5 and
  through Corollary 26.  d5(n) returns the largest power of four that is at most n^{1/18}, g5(D)
  returns ⌈D^{1/36}⌉, d26(n) returns ⌊n^{1/18}⌋, and g26(D) returns ⌈D^{0.0315}⌉; g5 and g26
  are for D ≥ 1 (`d5_spec`, `g5_spec`, `d26_spec`, `g26_spec`).
* queryCapNat(n, D) returns ⌊n²/√D⌋, and ceilDiv(a, b) returns ⌈a/b⌉ (`queryCapNat_meets`,
  `ceilDiv_meets`).

No routine touches the memory.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Comparing a power with a bound -/













namespace PowLt









end PowLt













/-! ## Roots, rounded up -/

namespace RootCeil







end RootCeil


















/-! ## The four parameters of the proof of Theorem 19 -/
















































































































/-! ## ⌊n²/√D⌋ and quotients rounded up -/












































































































end Light.Sec3

end
end

section


/-!
# Brute force (the proof of Theorem 19)

In the proof of Theorem 19, "smaller instances are solved by brute force": the procedure brute
(`bruteBody`) scans all of `C` for every pair `(a, b)` (`brute_spec`, `brute_meets`).  It takes at
most `100 n³ + 100` steps (`brute_solves`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}















namespace Brute














end Brute
























section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}





end















end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the need stays polynomial

The need of a procedure says what it asks of the limits of a run: the largest number that it forms,
the cells that it uses, and the depth of its calls.  If the need of the solver is polynomially
bounded (`PolyNeedN`), then so is the need of the host (`hostNeed_poly`: `PolyNeed` of `hostNeed`).
The need of the host is an explicit expression in `n`, `U`, `D`, `g` and a few quantities derived
from them.  Each of these is at most a polynomial in `(n + 1)(U + 1)` (`PolyBounded`), and such
bounds are closed under sums, products and powers.

* The quantities: `⌊√D⌋ ≤ D`, the number of binary digits of `U` is at most `U`,
  `2^{len + 1} ≤ 4(U + 1)`, `2^⌈log₂ n⌉ ≤ 2(n + 1)`, `⌊n²/√D⌋ ≤ n²`, `⌈s/g⌉ ≤ s + g` with
  `s = ⌊√D⌋`.
* The numbers (`polyBounded_hostWord`), the cells (`polyBounded_chooseCells`,
  `polyBounded_hostLayout`), and each of the three parts of the need of the solver on the instances
  of the host (`polyBounded_sup`).  The depth adds `O(⌈log₂ n⌉)` calls (`polyBounded_clog`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostPoly

/-! ## The quantities -/

















variable {D g : ℕ → ℕ}



/-! ## The numbers, the cells, and the solver -/

section parts

variable (hD : PolyBounded fun n _ => D n)
include hD









end parts

end HostPoly



end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the program, assembled

The procedures of the host are appended to a program `P₀` that already holds a solver of
Lop-AE-SparseTri and the two procedures that compute the parameters `D` and `g`.  This file has the
list of the procedures (`et17Procs`), their numbers (`et17NumsAt`), the proof that the program so
obtained is the context that the top procedure assumes (`et17Ctx_assembled`), and the
result: the host solves Exact Triangle (`et17_solves`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec




































































                                              -- 28

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}





end Light.Sec3

end
end

section


/-!
# Theorem 17 as a claim about programs of the light language

`Claim.Theorem_17 M MM D g` says: from every solver of Lop-AE-SparseTri with running time `T` there
is a solver of Exact Triangle whose running time is at most
`4ng (T + C n²/√D) + C (κ n³ log n/g + MM(n) D^{3/2} + n² D g)` (`bound17`, with the three terms
`termScans`, `termPrime`, `termBuild` of the additional time).  Here `κ` is the exponent in
`|w(e)| ≤ n^κ` (the paper's ν), `D` and `g` are the parameters of the reduction as functions of
`n`, `MM(n)` is the number of ring operations of the matrix multiplication, and `M` says what
"solved in time" means.
This file reduces the claim, for the interpretation by programs of the light language, to two facts
about a host: it turns solvers into solvers and keeps their need (word size, cells, depth of calls)
polynomial, and its time function obeys the bound (`ObeysBound17`, `claim17_of_host`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp


















end Light.Sec3

end
end

section


/-!
# Theorem 17: the time of each routine, up to a constant

The running time of the reduction of Theorem 17 is a sum of the time functions of its routines.  The
theorem bounds the additional time by "O(ν n³ log n/g + n^{ω+o(1)} D^{3/2} + n² D g)", where ν is
the exponent in `|w(e)| ≤ n^ν`; it is `κ` below.  The form for programs, `Claim.Theorem_17`, has,
here, Strassen's exponent `log₂ 7` in the second term.  This file bounds each
routine by a monomial in `n`, `√D` and `κ log n`, uniformly in `n`, `D`, `g`, `U` and `κ` under the
hypotheses of the theorem, and says which monomials are within which of the three terms.  No
constant is computed.

* `Steps t B` says that the number `t` of steps is `O(B)`, uniformly in the parameters.  Such bounds
  can be added and multiplied, and they absorb constant factors.
* Every time function is a polynomial in a few quantities, and each of these is at most a monomial
  `mon a b c = n^a (√D)^b (κ log n)^c`: `⌊√D⌋`, `g` and the size `⌈s/g⌉` of a piece are at most
  `√D`; `2^⌈log₂ n⌉ ≤ 2n`; the number of binary digits of `U ≤ n^κ` is `O(κ log n)` (section "The
  basic quantities").  So a routine takes `O(mon a b c)` steps (`StepsMon t a b c`), and the
  exponents are read off its time function, in the calculus `Scale.SoftO` on the scale `costScale`.
* All three bases are at least 1.  So a monomial is within the first term if its exponents are at
  most `(2, 1, 1)`, within the second if they are at most `(2, 3, 0)`, within the third if they are
  at most `(2, 2, 0)` (`Scale.SoftO.withinScans`, `Scale.SoftO.withinPrime`,
  `Scale.SoftO.withinBuild`).
* The choice of the prime runs through at most `√D` primes (`steps_chooseTime`).  The product of the
  two matrices is within the second term, as in the paper: Strassen's recursion makes
  `7^⌈log₂ n⌉ = O(n^{log₂ 7})` products of polynomials of degree below `p ≤ √D`
  (`steps_sqrt_mul_strSteps`).  The residues of the weights, computed bit by bit for each prime,
  take `O(√D n² κ log n)` steps, which is within the first term.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The hypotheses -/































namespace CostParams.Hyp

variable {θ : CostParams} (h : θ.Hyp)
include h












































end CostParams.Hyp

/-! ## Numbers of steps up to a constant -/






namespace Steps

variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}

























end Steps

/-! ## Monomials -/



















/-! ## The basic quantities -/

























































/-! ## The routines -/














































































/-! ## The three terms of the bound dominate the monomials -/






























































section within

variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}















end within

namespace Steps

variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}






end Steps

/-! ## The choice of the prime -/







































































end Light.Sec3

end
end

section


/-!
# Theorem 17 for programs of the light language, with the two choices of parameters of Section 3.3

Theorem 17 reduces Exact Triangle to at most `4ng` instances of Lop-AE-SparseTri(n, D). As
a claim about programs: from every solver of Lop-AE-SparseTri there is a solver of Exact Triangle
whose time obeys the bound of the theorem, here with Strassen's algorithm for the matrix product
(`Claim.Theorem_17` with `strassen`).  The program is the host `et17`.

The host takes the procedures that compute `D` from `n` and `g` from `D` as parameters.  Here they
are the routines for the two choices of the proof of Theorem 19: "Let D be the largest power of four
with D ≤ n^{1/18} [...] and let g := ⌈D^{1/36}⌉", and "Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉".
The program is the solver's program, followed by the parameter routines (`paramProcs`), followed by
the procedures of the host.

1. The four routines are parameter procedures in the sense of the host (`paramProc_d5`,
   `paramProc_g5`, `paramProc_d26`, `paramProc_g26`).
2. The parameters and the numbers that the routines form are polynomially bounded
   (`polyBounded_paramD₅Nat`, `polyBounded_paramG₅Nat`, `polyBounded_wD5`, `polyBounded_wG5`,
   and the same for the second choice).  So the need of the host (word size, cells, depth of calls)
   is polynomially bounded if that of the solver is (`hostNeed_poly`).  With `et17_solves` this
   makes the host turn solvers into solvers (`host_of_paramProcs`).
3. The routines take `O(n)`, respectively `O(D)`, steps (`steps_tD5`, `steps_tG5`, `steps_tD26`,
   `steps_tG26`).  So the time of the host obeys the bound of the theorem (`obeysBound17_hostTime`).
   Together: `claim_theorem_17₅` and `claim_theorem_17₂₆`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The parameter routines -/











































/-! ## The parameters and the words are polynomially bounded -/




































/-! ## The time of the parameter routines -/



















/-! ## The host with parameter routines -/















end Light.Sec3

end
end

section


/-!
# The running time of brute force (the proof of Theorem 19)

The `100 n³ + 100` steps of brute are within the form `C n³ (1 + log u)` in which the running times
for Exact Triangle with weights of absolute value at most `u` are stated (`claim_bruteForce`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec



end Light.Sec3

end
end

section


/-!
# Two programs in one: relocation of procedures

A program grows by appending procedures.  To put two programs, each with its own numbering of
procedures, into one, the second is placed behind the first (`Program.behind`), and the numbers of
the procedures that it calls are shifted by the length of the first (`Stmt.shift`).

A run of a statement in P is then a run of the shifted statement, with the same states and the
same number of steps (`Exec.shift`, an induction on the run in which only the case of a call has
anything to do: `Program.getElem?_behind_right`).  So everything proved with `Ends` carries over
(`Ends.shift`, `Ends.shift_append`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}






















end Light

end
end

section


/-!
# Two algorithms for Exact Triangle and a threshold on the number of vertices

For every threshold n₀ there is a constant C₀ such that, if Exact Triangle is solved in time T₁ and
in time T₂, then it is solved in time T₁ + C₀ for n < n₀ and T₂ + C₀ for n ≥ n₀.  This is
`Closure.ChooseBySize`, with "Exact Triangle is solved in time T" read as `SolvedIn etTask T`
(`closure_chooseBySize`).  It is used in the proof of Theorem 19, where the bounds hold
for large n only.

Two solvers are put into one program, the second behind the first (`solves_behind`), and one more
procedure looks at the number of vertices and calls the first solver below a fixed threshold n₀ and
the second one from the threshold on (`bySize_spec`).  The need stays polynomial
(`polyNeed_bySize`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}


















namespace ChooseHost







end ChooseHost

open ChooseHost



end Light.Sec3

end
end

section


/-!
# Corollary 15: counting triangles with the thin matrix product, and detecting with counting

Two steps of the proof of Corollary 15, with "the problem is solved in time T" read as
`ThinSolvedIn` and `LopSolvedIn`.

* `Claim.LopCountFromThinProduct`: "Apply Theorem 5 with N = n to the two biadjacency matrices".  An
  instance of #Lop-AE-SparseTri is given by its two biadjacency matrices, so a solver of the thin
  matrix product is a solver of #Lop-AE-SparseTri as it stands, called with U = 1, where U, the
  fourth argument and parameter, is the bound on the entries of the matrices
  (`solvesN_count_of_thin`, `claim_lopCountFromThinProduct`).
* `Claim.LopDetectFromCount`: the counts "are nonzero exactly for the query pairs that lie in a
  triangle".  One more procedure calls the counting solver and replaces every nonzero count by 1
  (`detect_spec`, `claim_lopDetectFromCount`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

namespace LopHosts

/-! ## Bounds -/





/-! ## Counting with the thin matrix product -/





end LopHosts

open LopHosts



/-! ## Detecting with counting -/

namespace LopArgs














end LopArgs
















namespace LopHosts







end LopHosts

open LopHosts



end Light.Sec3

end
end

section


/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}










namespace PowTable









end PowTable

open PowTable




































































end Light

end
end

section


/-!
# Theorem 5 in the light language: sizes and places

The sizes of the tables and arrays of Theorem 5's program, and their places in the memory. No
program occurs here.

The program for Theorem 5 (the solver) and the data structure of Section 4 begin with the same
stage, the shared stage, which fills the shared block: a directory of 32 cells with the sizes and
the addresses of the areas (`dirList`), then the tables, then the encodings of all bands, then two
scratch areas. The solver has a private block behind it. The areas lie one after the other:
`Par.places` (the shared block) and `Par.places5` (the private block) say where every area begins
and ends. `Par.sizes` collects the inequalities between the sizes, each of which has a name of its
own.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Sizes -/











namespace Par






















/-! ## The shared block, from its base address `b0` on -/











































end Par








/-! ## The private block of Theorem 5

The solver receives `N`, `D`, the number `w` of wanted positions, a bound `U` on the entries, the
addresses of `X`, `Y` (row by row), of the rows `WI` and the columns `WJ` of the wanted positions
and of the output, and as last argument the free pointer `fr`. All inputs and the output lie below
`fr`. The solver may write the output and the cells from `fr` on, and nothing is assumed about these
cells: a routine clears what it needs cleared. The shared block starts at `fr`, the private block
follows it. -/

namespace Par




























end Par

/-! ## The places and the sizes, as equations and inequalities -/



namespace Par
variable (p : Par)





























end Par











end Light.Sec2

end
end

section


/-!
# The alphabets of Schönhage's identity as digits

Section 2.2 names seven left variables, seven right variables, ten output variables and
ten terms; Section 2.3.1 indexes arrays by strings over these alphabets.  Here every
letter gets a digit, so that a string becomes a number (`codeStr`).

* The left variables `x₁ x₂ x₃ p₁₁ p₁₂ p₂₁ p₂₂` are the digits `0, …, 6`; likewise the right
  variables.
* The output variables `z₁₁ z₁₂ … z₃₃ z₀` are the digits `0, …, 9`, and the terms `P₁₁ … P₃₃ P₀`
  likewise, so that `z_ij` and `P_ij` have the same digit `3(i-1) + (j-1)`, and `z₀` and `P₀` have
  the digit 9.
* Left and right strings are numbers in base 7 (`codeL`, `codeR`), output strings, vertices and
  leaves in base 10 (`codeO`, `codeT`), strings of indices of outer variables in base 3
  (`codeOuter`) and of inner variables in base 4 (`codeInner`), always with level 1 most
  significant.
* Which output variables are inner, and which term contributes to which output variable (Section
  2.2), is read off the digits (`outVar_isInner_iff`, `contributes_iff`).
* The coefficients of the linear forms `φ_λ` and `ψ_λ` (Section 2.2) are written out as the rows of
  two 10 × 7 tables, `phiTable` and `psiTable`, which the programs store row after row
  (`phiFlat_spec`, `psiFlat_spec`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Digits -/





























































































/-! Applying one of the five bijections gives the digit. -/











/-! ## Codes of strings -/

























/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/




































/-! ## The structure of the identity, in digits -/

































/-! ## The coefficients of the linear forms, as tables -/





































end ThreeSumApsp.Spec

end
end

section


/-!
# Arrays on strings as lists

Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u that is
a left string of length L."  In a program such an array is a list: an array on the strings of length
`n` over an alphabet of `b` letters is the list of its `b^n` entries in the order of the codes
(`arrStr`), so the entry at a string is the entry of the list at the code of the string
(`getD_arrStr`), and an entry of the list is 0 if the array is 0 at the string with that code
(`getD_arrStr_eq_zero`).  The arrays on left strings, on right strings and on leaves are the cases
`arrL`, `arrR` and `arrT`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Arrays on the strings over any numbered alphabet -/

section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)


























end

/-! ## The three kinds of arrays of Section 2 that the programs store -/


































end ThreeSumApsp.Spec

end
end

section


/-!
# The memory map of Theorem 5: what depends on which cells

SharedReady.dirs lists the cells of the directory that the solver reads. SharedTables are the tables
of the shared block without the directory and the encodings; they depend only on the cells between
these two (SharedTables.congr), and all that the shared stage leaves behind depends only on the
cells of the shared block, without the last of the 32 cells of the directory, which the shared stage
does not use (SharedReady.congr, SharedReady.of_agree).
-/

public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The directory -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}























/-! ## Only the shared block matters -/












end Light.Sec2

end
end

section


/-!
# Theorem 30 in the light language: the memory map and the invariant of the data structure

The data structure occupies one block of the memory, from a base address b0 on. First comes the
shared block of Section 2 (directory, tables, the encodings of all bands), and behind it the areas
of Section 4:

    WD (L) | CUR (L) | BOX (L) | SS (m) | FP (1) | ROOTS (nB²) | TR (cap)

WD holds the digits of the output string of a query; CUR, BOX and SS are scratch strings; FP holds
the length of the trie array; ROOTS holds the roots of the tries, that of tile (β, β') in the cell
β nB + β'; TR is the trie area. Cell 31 of the directory holds t. `Areas` says where the tables that
the routines of Section 4 read and the areas of Section 4 lie, and `areas` proves it.

Two routines know this map: preCore(L, m, t, N, D, aX, aY, b0) builds the block from the matrices at
aX and aY, which lie below b0, and queryAt(I, J, b0) answers a query from it. They are relocatable,
so that Theorem 30, its offline form and Corollary 26 use the same two routines. The main procedures
of Theorem 30's programs only read the sizes from the input and compute the addresses. For Corollary
26 a routine of its own stands in between: it finds m and, from the threshold of the proof on, L and
t, writes padded copies of the matrices, and runs `preCore` on them.

Section 4.3: "Our data structure consists of three components: the list of the K₀² subsets Q
assigned to the block products of a tile […], the encodings of all row bands and all column bands,
and for every tile, the values of all its boxes". In the invariant DSReady the field shared holds
the first two, and the fields roots and trie hold the third: "for each tile we store its boxes, with
their values, in a standard trie on their strings of L symbols". The tries of all tiles lie in one
array (trie), and the table roots has the root of the trie of each tile. The invariant depends only
on the cells from b0 on, without the scratch strings (`DSReady.congr`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The map -/






















/-! ## Where the areas lie -/







































/-! ## The directory -/

namespace Dir




















end Dir

/-! ## The invariant -/



























section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}











end












/-! ## The two routines that know the map -/




































end Light.Sec4

end
end

section


/-!
# Section 4.4: the steps of the proof of Corollary 26 that hold for all parameters

The proof of Corollary 31 begins: "We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t :=
⌈θm⌉". This file has the parts of the proof of Corollary 26 that mention neither `L = 21m` nor
`t = ⌈m/9⌉`, under the headings of that proof. Both corollaries use them.

* Setting up. The inner dimension is padded to `D = 4^m` with `m = ⌈log_4 D⌉`
  (`Corollary26.setting_up`). This changes no entry of the product (`Corollary26.padding`), and it
  changes the bounds by a constant factor (`padded_le`). The switching order `t = ⌈θm⌉` is
  `switchOf θ m`, and `t ≤ m` (`switchOf_le`).
* Queries. `∑_{d ≤ t} α_d ≤ (9x)^t (1 + 1/x)^m` for every `x ≥ 1/9` (`sum_alpha_le`), and for
  `x = (1-θ)/θ` the right-hand side at `t = θm` is `D^q` (`rpow_mul_pow_eq_D_rpow_qOf`).
* Encodings. Inequality (10), whose left-hand side is `lhs10 L m γ`, bounds the last term of (8) and
  gives the hypothesis `N ≥ √K N₀` of Theorem 30 (`Equation10.last_term`, `Equation10.tile_fits`).
* Conclusion. The expression (8) from a bound on its first term and (10)
  (`dominated_cost8_of_eq_10`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given inner dimension, of `N` and of `m`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/




























































































/-! ### Queries -/









































/-! ### Encodings -/






























/-! ### Conclusion -/























end ThreeSumApsp

end
end

section


/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters and map -/









/-! ## The query -/

namespace Query31










end Query31





























end Light.Sec4

end
end

section


/-!
# Corollaries 26 and 31 in the light language: rational parameters in the program text

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D";
proof of Corollary 31: "with L := ⌈cm⌉ and t := ⌈θm⌉". A program is a finite text, so it can hold c
and θ only if they are rational: c = a/b and θ = p/q (`RatParams`). For real c and θ the statements
follow by approximation (`exists_ratParams`). Corollary 26 is the case c = 21, θ = 1/9, with the
threshold 60 (`ratParams26`).

This file has the parameters, what a structure at the free pointer fr consists of (`structEnd`,
`Ready31`), what the routines ask of the limits (`Lim31`), the query with its specification and its
proof (`QuerySpec31`, `query31_meets`), and the text and the specification of the preprocessing
(`pre31Body`, `PreSpec31`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters -/
















variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}


























































































































/-! ## The query: the text is query31Body -/




















/-! ## The preprocessing: text and interface -/









namespace Pre31



















end Pre31















































end Light.Sec4

end
end

section


/-!
# An entry of the product as an inner product

Proof of Corollary 26: "(For m < 60, D is bounded by a constant, and the corollary holds
trivially.)"; proof of Corollary 31: "for smaller m the corollary again holds trivially". In the
programs a query then computes an inner product, of a bounded number D of summands. The routine adds
the D products X[I, s] Y[s, J]. `ipPart` is the sum of the first s of them, with its recursion
(`ipPart_succ`), its bound (`abs_ipPart_le`) and its last value (`ipPart_full`); `ipAt_meets` is the
specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace IpAt















end IpAt











section
variable {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : Fin N)








variable {X Y}





end



end Light.Sec4

end
end

section


/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/








































/-! ## Configurations and single steps -/






















/-! ## Runs -/


















































/-! ## Pieces of code -/





































/-! ## Straight-line code -/





















































/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

















































end known

/-! ## Branches and verdicts -/























/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}






















































end framing

end ThreeSumApsp.WordRam

end
end

section


/-!
# Theorem 30, the offline form (9): preprocess, then one query for each wanted position

Theorem 30: "In particular, for every set W of positions of an N × N matrix, the entries (XY)[I, J],
(I, J) ∈ W, can be computed deterministically in time
O(L |W| ∑_{d=0}^{t} α_d + L m ρ^t/(1 - ρ) N² + N · 10^L/(√K N₀))."

wantedCore is relocatable: it receives the addresses of the matrices, of the two lists of indices,
of the output and of the free block. It meets its specification `WantedCoreSpec` in every program
that meets those of preCore and queryAt (`wantedCore_spec`): one call of preCore, then a loop whose
round asks one query and stores the answer (`wantedAsk_ends`), with the invariant `Answered`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## One query for each wanted position: the invariant -/

section
variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}
















end

/-! ## The routine -/



namespace WantedCore




















end WantedCore


















section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}


















end






















































































end Light.Sec4

end
end

section


/-!
# Section 4.4, the offline form: preprocess, then one query for each wanted position

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". Its proof: "The
bound for a set W follows by asking |W| queries." Proof of Theorem 25: "ask one query for each
position of W"; for Corollary 32 the paper uses "the same argument", "With Corollary 31 in place of
Theorem 24".

offline32(N, D, w, U, x, y, wi, wj, out, fr) preprocesses the matrices at x and y (pre31, which uses
the cells from the free pointer fr on) and then asks one query for each of the w positions, whose
rows are at wi and whose columns are at wj; the answers go to out. The arguments are those of the
task `thinTask`. The text `offline32Body`, with the round `offlineAsk32` of its loop, serves all
rational parameters c and θ: they are in the body of the procedure pre31 (`pre31Body`).

A round adds one answer (`offlineAsk32_ends`), with the invariant `Answered` that the offline form
of Theorem 30 uses too, and the routine meets its specification `OfflineSpec32` for all parameters G
(`offline32_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The text -/






namespace Offline32

















end Offline32















/-! ## What it does -/













































end Light.Sec4

end
end

section


/-!
# The routines of Section 4, assembled

The fourteen routines with the numbers 40 to 53, as a list (procs40), and the theorem that every
program that holds them at these numbers (Has40) meets all their specifications (specs40). Each
routine is proved under the specifications of the routines that it calls; here these assumptions are
discharged, in the order in which the routines call each other. For the programs of Theorem 30, its
offline form and Corollary 26, which hold the fourteen routines behind forty others
(has40_of_append), this gives the specifications of the two routines that know the memory map:
preCoreSpec_of and preCoreSpec_all for the preprocessing, queryAtSpec_all for a query.
-/

@[expose] public section

namespace Light.Sec4





































































end Light.Sec4

end
end

section


/-!
# Theorem 30 on the word RAM: the program

`program30` is the list of procedures: those of Section 2 (numbers 0 to 28, of which the
preprocessing uses the shared stage), the routines of Section 4 (40 to 53), preCore, queryAt and the
two procedures of the offline form (54 to 57), and the two main procedures of Theorem 30 (80 and
81); the unused numbers hold the empty statement.

The first 58 procedures (`base58`) are also the beginning of the programs for Corollaries 26, 31
and 32.  So the assumptions of the earlier files are discharged for every program `base58 ++ R` that
begins with them: it meets the specifications of the preprocessing and of a query at a given place
of the memory (`preCore_base58`, `queryAt_base58`).  With `theorem_30_of` and `theorem_30_wanted_of`
this gives Theorem 30 and its offline form without hypotheses (`wordRam_theorem_30`,
`wordRam_theorem_30_wanted`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam





































end Light.Sec4

end
end

section


/-!
# Corollaries 26, 31 and 32: the concrete program for given parameters

program31 G = base58 (Theorem 5's and Theorem 30's procedures, numbers 0 to 57) followed by the
procedures 58 to 73 of Section 4.4 (`procs31`): copying, filling, m = ⌈log₄ D⌉, padding and the
inner product; the preprocessing pre31Body G at 64 and the query; their main procedures; the offline
routine and its main procedure; the solver of Corollary 26 for all instances with its test; and the
two procedures for L = ⌈am/b⌉ and t = ⌈pm/q⌉ at 72 and 73. The specifications of the preprocessing,
the query and the offline routine hold for it, for all limits, without hypotheses. At the parameters
of Corollary 26 it is `program26`.

With the two end theorems for light programs and the compiler this gives the two statements about
the word RAM from which Corollaries 26, 31 and 32 follow: on every domain of inputs, and for all
bounds that dominate the two costs of Theorem 30 at the parameters G (`CostsWithin`), the compiled
program is a data structure (`isDataStructure_of_costsWithin`) and solves the offline problem
(`solves_of_costsWithin`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/












/-! ## The program -/











































/-! ## The program on the word RAM -/







































end Light.Sec4

end
end

section


/-!
# Corollary 26, the offline form, on all instances

Corollary 26 is about matrices with N ≥ D^18. A solver that other procedures call has to be right on
every instance. allInstances26(N, D, w, U, x, y, wi, wj, out, fr) tests whether D^18 ≤ N, calls the
offline routine offline32 if so and the brute force if not. The texts are `allInstances26Body` and
`regimeTest26Body`.

* *The routine.* It solves the task `thinTask` on every instance, within the time
  `allInstancesTime26` and the need `allInstancesNeed26` (`allInstances26_solves`). It tests whether
  D^18 ≤ N (`regimeTest26_meets`). In that regime it calls the offline routine of Corollary 26,
  whose demands on the limits are covered by the need (`lim31_of_need`, `offline32_meets_thinTask`);
  outside it calls the brute force.
* *The time in the regime.* For N ≥ D^18 the time is O(w D^{0.437} + N²/D^{0.063}), the bound of
  Corollary 26: the time of the offline routine is at most a constant times tp + w tq for all bounds
  that dominate the two costs of Theorem 30 (`exists_tOffline32_le`), and in the regime the two
  bounds of Corollary 26 do (`regime26`).
* *The need is polynomial in the parameters.* Every summand of the need is a numeral times a product
  of at most 20 factors N + 1, D and U. With Q = (N + 1) (D + 1) (w + 1) (U + 1) each factor is at
  most Q, so each product is at most Q^20 (`le_pow_twenty`). So the largest number, the cells and
  the levels of calls are at most 2^11 Q^20 (`word_le`, `cells_le`, `depth_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Time and need -/


















/-! ## The test -/





















/-! ## The limits -/

section need

variable {lim : Limits} {N D₀ w U fr d : ℕ}










































































end need

/-! ## The matrices of an instance -/



































/-! ## The routine -/


























































































/-! ## The time in the regime -/


















/-! ## The need is polynomial in the parameters -/



section summands

variable {N D U Q : ℕ}







end summands





end Light.Sec4

end
end

section


/-!
# Corollary 26, the offline form, for programs of the light language

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". This is
`Claim.Corollary_26_wanted`, here with "is solved in time T" read as a statement about programs of
the light language (`claim_corollary_26_wanted`).

The program is `program26`: for m = ⌈log₄ D⌉ ≥ 60 it builds and asks the data structure of Theorem
30 with L = 21 m and t = ⌈m/9⌉, and for m < 60 it computes inner products. The procedure
allInstances26 of that program solves the task on all instances (`allInstances26_program26`), with a
polynomially bounded need (`allInstancesNeed26_poly`), and for N ≥ D^18 its time is within the bound
(`allInstancesTime26_le`).

This is the form of Corollary 26 on which Corollary 16, and through it the second bounds of Theorems
19 and 22, rest: a procedure that other procedures call. The statement about one program that reads
the input of the problem is `wordRam_corollary_26_wanted`.
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec







end Light.Sec4

end
end

section


/-!
# From a realized running time to a program with the paper's bound

A claim gives a running time `T` with `T ≤ C X`, where `X` is the bound that the paper prints, and
`RealizedWithin` gives a program that takes `c T + c` steps.  This file puts the two together.

* Bounds in several parameters, valid on a domain on which `X ≥ 1`: `exists_solves`, and
  `exists_solves_nonneg` with `exists_solves_pair` for two programs with one slope and one constant.
* Bounds `O(n^a (log n)^e)` in one size, valid for all large `n`: `solvedAt_of_realized`, and for
  every exponent `κ` of the magnitude `solvedInTime_of_claim` and `solvedInPolylogTime_of_claim`.
* An instance with numbers bounded by `n^κ` is also one with numbers bounded by `n^κ'`, `κ ≤ κ'`
  (`solvedInTimeAt_mono`), so that a bound for all `κ ≥ 1` is a bound for all `κ`
  (`solvedInTime_of_one_le`).
-/

public section

namespace ThreeSumApsp.FromClaims

open ThreeSumApsp.WordRam
open EndStatement (Instr)

/-! ## Bounds on a domain -/




















































/-! ## Bounds in one size, for all large sizes -/


































/-- A claim "solved in `O(n^a (log n)^{O(1)})` time on numbers of absolute value at most `n^κ`, for
every `κ`", in a reading `S` of "is solved in time T" that is realized, gives programs. -/
theorem solvedInPolylogTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperPowPolylog a) :
    SolvedInPolylogTime Q a := by
  intro κ
  obtain ⟨T, hT, C, e, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact ⟨e, solvedAt_of_realized T κ (hR T hT) hb⟩






















end ThreeSumApsp.FromClaims

end
end

section


/-!
# Running-time claims of Section 3.1: Corollaries 15 and 16

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".

* Corollary 15, first case, from Theorem 5 ("Apply Theorem 5 with N = n to the two biadjacency
  matrices"): `Corollary15.first_of_theorem_5`.
* Corollary 15, general case ("splitting W into sets of at most n²/√D query pairs"):
  `Corollary15.general_of_theorem_5`.  One call costs `O(n² log² D / D^{1/18})`, and all calls
  with the overhead cost `O((n² + |W| √D) log² D / D^{1/18})` (`dominated_calls`).
* Corollary 16 from Corollary 26 ("This is Corollary 26 with N = n"):
  `Corollary16.of_corollary_26`.

In each deduction the overheads `n D`, `|W|` and `1` of writing the matrices and copying the answers
are at most the bound of the corollary, because `n ≥ D^18`.  The bounds are added up by the calculus
of `Dominated` on the parameters `n`, `D`, `w`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## The calculus on the parameters `n`, `D`, `w` -/













/-! ## Corollary 15, the first case -/























/-! ## Corollary 15, the general case -/





















































/-! ## Corollary 16 -/



end ThreeSumApsp

end
end

section


/-!
# Corollaries 15 and 16 on the word RAM

The route, as in the paper.  The number of triangles through a query pair is an entry of the product
of the two biadjacency matrices, and detection follows from counting.  So Theorem 5 gives the first
case of Corollary 15; splitting the query pairs into pieces gives the general case; and the offline
form of Corollary 26 gives Corollary 16.  These are claims about programs of the light language
(`claim_corollary_15_first`, `claim_corollary_15`, `claim_corollary_16`).  The outermost procedures
for the input layout and the compiler (`Light.Sec3.realized_lopCount`,
`Light.Sec3.realized_lopDetect`, together `lopRealized`) carry them to the word RAM.
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3


















end Light.Sec3

namespace ThreeSumApsp









end ThreeSumApsp

end
end

section


/-!
# The cost analysis of Theorem 19 for a general choice of the parameters

The two halves of the proof of Theorem 19 are the same computation with different numbers.  Both
apply Theorem 17 with a number `D ≥ 16` between `n^{1/18}/c` and `n^{1/18}` and with `g = ⌈D^η⌉`,
and solve each of the at most `4ng` instances with a saving `D^{2η}`.  Such a pair `D`, `η` is a
`Choice`, and the computation is carried out here for every choice.

1. A choice satisfies the hypotheses `16 ≤ D ≤ n` and `1 ≤ g ≤ √D` of Theorem 17 and the hypothesis
   `D^18 ≤ n` of Corollaries 15 and 16 (`Choice.sixteen_le`, `Choice.le_n`, `Choice.one_le_ceil`,
   `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. The lower bound on `D` gives `D^{-η} ≤ c^η n^{-η/18}` (`Choice.saving`), and the upper bound
   gives `D^a ≤ n^{a/18}` (`Choice.rpow_le_rpow_div`).
3. Each of the four terms of the running time is `O(n^{3-η/18})` up to logarithms: the instances
   (`Choice.instances_le`) and the scans (`Choice.scans_le`) by the first bound, the choice of `p`
   (`Choice.strassen_le`) and building the instances (`Choice.build_le`) by the second.
4. So is their sum (`exists_total_le`).
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem19





















namespace Choice

variable {n D : ℕ} {η c : ℝ} (P : Choice n D η c)
include P

/-! ### The hypotheses of Theorem 17 and of Corollaries 15 and 16 -/




































/-! ### Logarithms -/







/-! ### Powers of `D` in terms of `n` -/









/-! ### The four terms of the running time

`Λ` is the logarithmic factor of the result, `log² n` or `log n`. -/









end Choice



end Theorem19

end ThreeSumApsp

end
end

section


/-!
# Theorem 19 and Remark 20: Exact Triangle in truly subcubic time (Section 3.3)

Theorem 19 applies the reduction of Theorem 17 with `D` about `n^{1/18}` and `g = ⌈D^η⌉`, and solves
each instance by a corollary of Section 3.1: by Corollary 15 with `η = 1/36`, where `D` is the
largest power of four with `D ≤ n^{1/18}`, and by Corollary 16 with `η = 0.0315`, where
`D = ⌊n^{1/18}⌋`.  This file has the arithmetic of the proof.  The deduction of the running time
from Theorem 17 that uses it is `Theorem19.explicit_of_theorem_17_corollary_15` and
`Theorem19.explicit_of_theorem_17_corollary_16`, and the theorem about programs is
`wordRam_theorem_19`.

1. Both choices of the parameters, `paramD₅` with `paramG₅` and `paramD₂₆` with `paramG₂₆`, are a
   `Theorem19.Choice` (`Theorem19.choice_theorem_5`, `Theorem19.choice_corollary_26`).  So they
   satisfy the hypotheses of Theorem 17 and of the two corollaries (`Choice.sixteen_le`,
   `Choice.le_n`, `Choice.one_le_ceil`, `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. By the cost analysis for a general choice (`Theorem19.exists_total_le`), the number of instances
   times the cost of one instance, plus the additional time of Theorem 17, is
   `O(n^{3-1/648} log² n)`, respectively `O(n^{3-0.00175} log n)` (`Theorem19.total_theorem_5`,
   `Theorem19.total_corollary_26`).  The step "O(n^{3−ε'} log n) ≤ O(n^{3−ε_T})" of the
   statement is the general fact that a larger exponent absorbs logarithms
   (`IsPowPolylog.isBigOPow`); it is applied in `Theorem19.second_of_explicit`.

NOTE.  "Assume n is larger than a constant depending on ν": the two choices of `D` below are stated
for `n ≥ 16^18`, which makes `D ≥ 16`.

Remark 20 explains the values of `η`: the exponents `η - γ` of the instances and `-η` of the scans
balance at `η = γ/2` (`remark_20_balance`, `remark_20_numbers`), and the straightforward algorithm
for the instances gives back the bound `n³` (`remark_20_brute_force`).
-/

public section

namespace ThreeSumApsp

/-! ### The two choices of the parameters -/













































/-! ### The costs added up -/

























/-! ### Remark 20 -/









































end ThreeSumApsp

end
end

section


/-!
# Theorem 19 from Theorem 17 and Corollaries 15 and 16

Theorem 17 reduces Exact Triangle to `4 n g` calls of Lop-AE-SparseTri plus some extra time.  The
proof of Theorem 19 puts in the cost of one call (Corollary 15 or Corollary 16) and the parameters
`D` and `g`, and adds up.  Both routes have the same three steps:

1. the parameters satisfy the hypotheses of Theorem 17 and of the corollary (`Theorem19.choice_*`);
2. one call, with the reading of its answers, costs `O(I)` (`call_cost_corollary_15` and
   `call_cost_corollary_16`);
3. the sum of all terms is `O(κ P)` (`Theorem19.total_*`, the calculation of the proof of
   Theorem 19).

`time_le_of_calls` puts the three steps together.  The result keeps the dependence on `κ`
(`Claim.Theorem_19_explicit`).  From it follow the two bounds as printed, for every constant `κ`
(`Claim.Theorem_19_explicit.eventually_le`), and a bound for all sizes and all bounds on the
weights, which is what Theorem 21 is applied to (`exactTriangleUniform_of_explicit`): small sizes by
brute force (`dominated_bruteForce`), large sizes by the explicit bound with
`κ = max 1 (log u / log s)` (`dominated_explicit`).
-/

@[expose] public section

namespace ThreeSumApsp







































/-! ## The bounds as printed -/





































/-! ## A bound for all sizes and all bounds on the weights -/
























end ThreeSumApsp

end
end

section


/-!
# Theorem 19 on the word RAM

The route, as in the paper.  Theorem 17 reduces Exact Triangle to instances of the lopsided triangle
problem.  With the parameters `D` and `g` of Section 3.3 and Corollary 15 for the instances the
total is `O(n^{3−1/648} log² n)` (`claim_theorem_19_usingTheorem5`); with Corollary 16 it is
`O(n^{3−ε'} log n)`, `ε' = 0.00175` (`claim_theorem_19_usingCorollary26`).  Both are claims about
programs of the light language that keep the dependence on `κ`.  The outermost procedure for the
input layout and the compiler (`Light.Sec3.realized_exactTriangle`) carry them to the word RAM.
The third bound of the theorem, `O(n^{3−ε_T})`, follows from the second, so it rests on Corollary 16
and not on Corollary 15.

Section 3.4 needs the two bounds for all numbers of vertices and all bounds on the weights:
`claim_exactTriangleUniform_usingTheorem5`, `claim_exactTriangleUniform_usingCorollary26`.  They
combine the program with brute force below a threshold, as in the proof ("smaller instances are
solved by brute force").
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

















end Light.Sec3

namespace ThreeSumApsp












end ThreeSumApsp

end
end

section


/-!
# APSP: from a solver of the task to a program for the layout of the end statement

APSP (Theorem 22).  `realized_apsp`: if the task `apTask` is solved in time T, then
`EndStatement.APSP` is solved on the word RAM within a constant times T.

The input is n in cell 0, the adjacency matrix from cell 1 and the weights from cell 1 + n².  The
answer goes to the 2n² cells from 1 + 2n², and the free pointer is 1 + 4n² (`apspInst`).  The task
speaks of the graph with weights in `WithTop ℤ` that is read from the two lists, which is the graph
of the instance (`graphOf_apsp`).  So the input meets the task's precondition (`pre_apsp`), and what
a solver leaves in the output cells is what `EndStatement.APSP` asks for (`post_apsp`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.WordRam ThreeSumApsp.Spec































































































/-- **APSP**: if the task is solved in time T, then APSP is solved on the word RAM within a constant
times T. -/
theorem realized_apsp (T : ℕ → ℝ → ℝ) (h : SolvedIn apTask T) :
    Realized EndStatement.APSP T :=
  wrapApsp.realized h

end Light.Sec3

end
end

section


/-!
# Running-time claims of Section 3.4: Theorems 21 and 22

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".  They
are deductions between running-time sentences: those of the paper for Theorem 22, and for
Theorem 21, which the paper cites, those of the route taken here.

* Theorem 21(a) from two reductions, [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]:
  `Theorem21a.of_CH20_VW13`.  The sizes, numbers of instances and extra times compose
  by the rules for `n^{a+o(1)}`.
* Theorem 21(b) for the (min,+)-product from [VW13, Theorem 3.3] and [VW18, Theorem 4.2]:
  `Theorem21b.minPlus_of_VW13_VW18`.  The time of the first reduction is again a good
  time (`GoodTime.mul_logU`), and `log (cU) = O(log U)` (`dominated_logU_mul`).
* Theorem 21(b) for APSP by repeated squaring: `Theorem21b.apsp_of_minPlus`, whose
  arithmetic is `dominated_repeatedSquaring`.
* "Plug Theorem 19 into Theorem 21": `threeSum_of_uniform_theorem_21a`,
  `minPlus_of_uniform_theorem_21b`, `apsp_of_uniform_theorem_21b`.
* Theorem 22: the roundings such as `n^{2-1/1296+o(1)} ≤ O(n^{1.99923})`
  (`Claim.SolvedAlongPow.mono`).
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Theorem 21(a) -/




























/-! ## Theorem 21(b): the (min,+)-product -/

/-- A good time is at least `1 + log u`. -/
theorem GoodTime.one_add_logU_le {T : ℕ → ℝ → ℝ} (hT : GoodTime T) {s : ℕ} (hs : 1 ≤ s) (u : ℝ) :
    1 + logU u ≤ T s u :=
  (le_mul_of_one_le_left (zero_le_one.trans (one_le_one_add_logU u))
    (one_le_pow₀ (Nat.one_le_cast.2 hs))).trans (hT.1 s u hs)

/-- A good time is nonnegative. -/
theorem GoodTime.nonneg {T : ℕ → ℝ → ℝ} (hT : GoodTime T) {s : ℕ} (hs : 1 ≤ s) (u : ℝ) :
    0 ≤ T s u :=
  (zero_le_one.trans (one_le_one_add_logU u)).trans (hT.one_add_logU_le hs u)

/-- The time `C T(s) log U` that [VW13, Theorem 3.3] gives for Negative Triangle is again a good
time. -/
theorem GoodTime.mul_logU {T : ℕ → ℝ → ℝ} (hT : GoodTime T) {c C : ℝ} (hc : 1 ≤ c) (hC : 2 ≤ C) :
    GoodTime fun s U => C * (T s (c * U) * logU U) := by
  refine ⟨fun s u hs => ?_, fun u s₁ s₂ hs₁ hs => ?_⟩
  · have hT0 := hT.nonneg hs (c * u)
    have hhalf : 1 / 2 ≤ logU u := Real.one_half_lt_log_two.le.trans (log_two_le_logU u)
    calc (s : ℝ) ^ 2 * (1 + logU u) ≤ (s : ℝ) ^ 2 * (1 + logU (c * u)) := by
          gcongr
          exact logU_le_logU_mul hc u
      _ ≤ T s (c * u) := hT.1 s _ hs
      _ = 2 * (T s (c * u) * (1 / 2)) := by ring
      _ ≤ C * (T s (c * u) * logU u) := by gcongr
  · calc C * (T s₁ (c * u) * logU u) / s₁ = C * logU u * (T s₁ (c * u) / s₁) := by ring
      _ ≤ C * logU u * (T s₂ (c * u) / s₂) :=
          mul_le_mul_of_nonneg_left (hT.2 (c * u) s₁ s₂ hs₁ hs)
            (mul_nonneg (zero_le_two.trans hC) (logU_pos u).le)
      _ = C * (T s₂ (c * u) * logU u) / s₂ := by ring

/-- Theorem 21(b), (min,+)-product, from two reductions: [VW13, Theorem 3.3] followed by
[VW18, Theorem 4.2]. -/
theorem Theorem21b.minPlus_of_VW13_VW18 (M : DetTimeModel)
    (h33 : Claim.VW13_Theorem_3_3 M) (h42 : Claim.VW18_Theorem_4_2 M) :
    Claim.Theorem_21b_minPlus M := by
  obtain ⟨c₁, C₁, hc₁, hC₁, h33⟩ := h33
  obtain ⟨c₂, C₂, hc₂, hC₂, h42⟩ := h42
  obtain ⟨B, hB0, hB⟩ := dominated_logU_mul hc₂
  refine ⟨c₁ * c₂, C₂ * (C₁ * B), one_le_mul_of_one_le_of_one_le hc₁ hc₂, fun T hT hex => ?_⟩
  obtain ⟨T'', hT'', hb⟩ := h42 _ (hT.mul_logU hc₁ hC₁) (h33 T hT hex)
  refine ⟨T'', hT'', fun n U hn hU => ?_⟩
  have hT0 := hT.nonneg (one_le_cbrtCeil hn) (c₁ * (c₂ * U))
  have hC₁0 : 0 ≤ C₁ := zero_le_two.trans hC₁
  have hlogU := (logU_pos U).le
  have hlogcU := (logU_pos (c₂ * U)).le
  calc T'' n U
      ≤ C₂ * ((n : ℝ) ^ 2 * (C₁ * (T (cbrtCeil n) (c₁ * (c₂ * U)) * logU (c₂ * U))) * logU U) :=
        hb n U hn hU
    _ ≤ C₂ * ((n : ℝ) ^ 2 * (C₁ * (T (cbrtCeil n) (c₁ * (c₂ * U)) * (B * logU U))) * logU U) := by
        gcongr
        exact hB U trivial
    _ = C₂ * (C₁ * B) * ((n : ℝ) ^ 2 * T (cbrtCeil n) (c₁ * c₂ * U) * logU U ^ 2) := by
        rw [mul_assoc c₁ c₂ U]
        ring

/-! ## Theorem 21(b): APSP -/










/-- The arithmetic of repeated squaring:
`(⌈log₂ n⌉ + 1) (C n² V W² + C₀ n² (1 + W)) = O(n² V log³ n)`, if `0 ≤ W ≤ B log n` and
`V ≥ 1 + W`. -/
private theorem dominated_repeatedSquaring (C C₀ : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    Dominated (fun p : Squaring => 2 ≤ p.n ∧ 0 ≤ p.W ∧ p.W ≤ B * Real.log p.n ∧ 1 + p.W ≤ p.V)
      (fun p => ((Nat.clog 2 p.n : ℝ) + 1) *
        (C * ((p.n : ℝ) ^ 2 * p.V * p.W ^ 2) + C₀ * ((p.n : ℝ) ^ 2 * (1 + p.W))))
      fun p => (p.n : ℝ) ^ 2 * p.V * Real.log p.n ^ 3 := by
  set dom : Squaring → Prop := fun p =>
    2 ≤ p.n ∧ 0 ≤ p.W ∧ p.W ≤ B * Real.log p.n ∧ 1 + p.W ≤ p.V
  have hV0 : ∀ p, dom p → 0 ≤ (p.n : ℝ) ^ 2 * p.V := fun p ⟨_, hW0, _, hV⟩ =>
    mul_nonneg (by positivity) ((add_nonneg zero_le_one hW0).trans hV)
  have hrounds : Dominated dom (fun p => (Nat.clog 2 p.n : ℝ) + 1) fun p => Real.log p.n :=
    (dominated_clog_add_one_log 2).comp Squaring.n fun _ hp => hp.1
  have hW : Dominated dom Squaring.W fun p => Real.log p.n :=
    .of_le_const_mul hB fun _ hp => hp.2.2.1
  have hone : Dominated dom (fun _ => (1 : ℝ)) fun p => Real.log p.n ^ 2 :=
    .of_le_const_mul (C := 4) (by norm_num) fun p hp => by
      nlinarith [Real.one_half_le_log_of_two_le (Nat.ofNat_le_cast.2 hp.1 : (2 : ℝ) ≤ p.n)]
  -- one product: `C n² V W² = O(n² V log² n)`
  have hproduct : Dominated dom (fun p => C * ((p.n : ℝ) ^ 2 * p.V * p.W ^ 2))
      fun p => (p.n : ℝ) ^ 2 * p.V * Real.log p.n ^ 2 :=
    ((hW.pow (fun _ hp => hp.2.1) 2).mul_left hV0).const_mul_of_nonneg C fun p hp =>
      mul_nonneg (hV0 p hp) (by positivity)
  -- writing a matrix: `C₀ n² (1 + W) ≤ C₀ n² V = O(n² V log² n)`
  have hwrite : Dominated dom (fun p => C₀ * ((p.n : ℝ) ^ 2 * (1 + p.W)))
      fun p => (p.n : ℝ) ^ 2 * p.V * Real.log p.n ^ 2 :=
    (((hone.mul_left hV0).congr (fun _ _ => mul_one _) fun _ _ => rfl).mono_left fun p hp =>
      mul_le_mul_of_nonneg_left hp.2.2.2 (by positivity)).const_mul_of_nonneg C₀ fun p hp =>
        mul_nonneg (by positivity) (add_nonneg zero_le_one hp.2.1)
  -- `⌈log₂ n⌉ + 1 = O(log n)` rounds
  exact (((hproduct.add hwrite).mul_left fun p _ => by positivity).trans
    (hrounds.mul_right fun p hp => mul_nonneg (hV0 p hp) (by positivity))).congr
      (fun _ _ => rfl) fun _ _ => by ring

/-- Theorem 21(b), APSP: repeated squaring on top of the
(min,+)-product. -/
theorem Theorem21b.apsp_of_minPlus (M : DetTimeModel) (h21 : Claim.Theorem_21b_minPlus M)
    (hsq : Claim.ApspFromMinPlus M) : Claim.Theorem_21b_apsp M := by
  obtain ⟨c, C, hc, h21⟩ := h21
  obtain ⟨ca, C₀, hca, hsq⟩ := hsq
  intro κ hκ
  obtain ⟨B, hB0, hB⟩ := dominated_logU_mul_rpow hca (by linarith : 0 ≤ κ + 1)
  obtain ⟨K, -, hK⟩ := dominated_repeatedSquaring C C₀ hB0
  refine ⟨c * ca, K, one_le_mul_of_one_le_of_one_le hc hca, fun T hT hex => ?_⟩
  obtain ⟨T', hT', hb⟩ := h21 T hT hex
  refine ⟨_, hsq T' hT', fun n hn => ?_⟩
  have hn1 : 1 ≤ n := one_le_two.trans hn
  have hpow : (n : ℝ) * (n : ℝ) ^ κ = (n : ℝ) ^ (κ + 1) := by
    rw [Real.rpow_add_one (Nat.cast_pos.2 hn1).ne', mul_comm]
  -- the finite entries are at most n^{κ+1} in absolute value
  have hproduct := hb n (ca * (n : ℝ) ^ (κ + 1)) hn1 (one_le_mul_of_one_le_of_one_le hca
    (Real.one_le_rpow (Nat.one_le_cast.2 hn1) (by linarith)))
  have hV : 1 + logU (ca * (n : ℝ) ^ (κ + 1)) ≤ T (cbrtCeil n) (c * (ca * (n : ℝ) ^ (κ + 1))) :=
    (add_le_add_right (logU_le_logU_mul hc _) 1).trans
      (hT.one_add_logU_le (one_le_cbrtCeil hn1) _)
  have htotal := hK ⟨n, T (cbrtCeil n) (c * (ca * (n : ℝ) ^ (κ + 1))), _⟩
    ⟨hn, (logU_pos _).le, hB n hn, hV⟩
  rw [hpow, mul_assoc c ca]
  exact (mul_le_mul_of_nonneg_left (add_le_add_left hproduct _) (by positivity)).trans htotal

/-! ## "Plug Theorem 19 into Theorem 21"

The time of Theorem 19 is `uniformTime K δ e s u = K s^{3-δ} (log s + 1)^e (1 + log u)²`.
Theorem 21 evaluates it at sizes `s(n)` and bounds `u(n) ≤ c n^κ` on the numbers, and multiplies it
by powers of `n` and logarithms.  So each bound is a product of functions of known classes. -/






























/-- The time of Theorem 19 on `⌈n^{1/3}⌉` vertices per part, with weights up to `c n^κ`, is
`Õ(n^{1-δ/3})`. -/
theorem isPowPolylog_uniformTime_cbrtCeil (K : ℝ) {δ : ℝ} (e : ℕ) (hδ : δ ≤ 3) {c κ : ℝ}
    (hc : 1 ≤ c) (hκ : 0 ≤ κ) :
    IsPowPolylog (fun n : ℕ => uniformTime K δ e (cbrtCeil n) (c * (n : ℝ) ^ κ)) (1 - δ / 3) := by
  have hsize := (isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).comp
    (isBigOPow_ceil_rpow (μ := 1 / 3) (by norm_num)) (by linarith) (by norm_num)
  have hwords := ((isPowPolylog_const 1).add (isPowPolylog_logU_mul_rpow hc hκ)).pow 2
  exact ((hsize.mul hwords).const_mul K).mono (le_of_eq (by push_cast; ring))






































/-- "Plug Theorem 19 into Theorem 21", APSP, in general form. -/
theorem apsp_of_uniform_theorem_21b (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21b_apsp M) :
    Claim.ApspInPolylog M (3 - δ / 3) := by
  obtain ⟨K, hK, hex⟩ := hu
  intro κ hκ
  obtain ⟨c, C, hc, h21⟩ := h21 κ hκ
  obtain ⟨T', hT', hb⟩ := h21 _ (goodTime_uniformTime e hK hδ1) hex
  have htotal := ((((isBigOPow_natCast_pow 2).isPowPolylog.mul
    (isPowPolylog_uniformTime_cbrtCeil K (δ := δ) e (by linarith) hc (by linarith : 0 ≤ κ + 1))).mul
    (isPowPolylog_log_pow 3)).const_mul C).mono (b := 3 - δ / 3) (le_of_eq (by push_cast; ring))
  exact ⟨T', hT', htotal.upperPowPolylog.mono_left (Filter.eventually_atTop.2 ⟨2, hb⟩)⟩

/-! ## Theorem 22 -/









end ThreeSumApsp

end
end

section


/-!
# Theorem 22 on the word RAM

"Plug Theorem 19 into Theorem 21."  Each bound has three ingredients.

1. The paper's deduction between running times, proved for every reading `M` of the sentence "is
   solved by a deterministic algorithm in time T" (lemmas such as `threeSum_of_uniform_theorem_21a`;
   nothing is assumed about `M`).
2. The reading `lightModel`, in which the sentence means that a program of the light language solves
   the task within T steps.  For this reading the reductions that Theorem 21 cites are theorems,
   because they are written as programs that call an arbitrary solver (`Sec3.claim_…`); so
   Theorem 21 holds for it: `claim_theorem_21a` for 3SUM, `claim_theorem_21b_minPlus` and
   `claim_theorem_21b_apsp` for the (min,+)-product and APSP.
3. The way to the machine: a solver of a task, with one more procedure for the input layout,
   compiled, is a program of the word RAM that takes a constant times as many steps
   (`Sec3.realized_threeSum`, `realized_minPlusProduct`, `realized_apsp`).

From a bound `O(s^{3−δ} (log s)^e)` for Exact Triangle this gives

* 3SUM in `O(n^a)` time for every `a > 2 − δ/2` (`threeSum_of_uniform`);
* the (min,+)-product and APSP in `O(n^{3−δ/3} (log n)^{O(1)})` time (`minPlus_polylog_of_uniform`,
  `apsp_polylog_of_uniform`), and so in `O(n^a)` time for every `a > 3 − δ/3`
  (`SolvedInPolylogTime.solvedInTime`).

The theorem is the case `δ = 1/648` (using Theorem 5) and the case `δ = ε' = 0.00175` (using
Corollary 26).  For 3SUM the programs lose polylogarithmic factors only
(`Theorem22.threeSum_polylog`); the printed form with `n^{o(1)}` follows
(`SolvedInPolylogTime.solvedInLittleOTime`).
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

/-! ## Theorem 21 for programs of the light language -/






/-- Theorem 21(b): the (min,+)-product from Exact Triangle, through Negative Triangle. -/
theorem claim_theorem_21b_minPlus : Claim.Theorem_21b_minPlus lightModel :=
  Theorem21b.minPlus_of_VW13_VW18 _ claim_VW13_Theorem_3_3
    claim_VW18_Theorem_4_2

/-- Theorem 21(b): APSP from Exact Triangle, through the (min,+)-product. -/
theorem claim_theorem_21b_apsp : Claim.Theorem_21b_apsp lightModel :=
  Theorem21b.apsp_of_minPlus _ claim_theorem_21b_minPlus claim_apspFromMinPlus

/-! ## A bound for Exact Triangle, plugged into Theorem 21 -/
















/-- APSP in `O(n^{3−δ/3} (log n)^{O(1)})` time. -/
theorem apsp_polylog_of_uniform {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform lightModel δ e) :
    SolvedInPolylogTime EndStatement.APSP (3 - δ / 3) :=
  FromClaims.solvedInPolylogTime_of_claim realized_apsp
    (apsp_of_uniform_theorem_21b _ e hδ hu claim_theorem_21b_apsp)

end Light.Sec3

namespace ThreeSumApsp





















































end ThreeSumApsp

end
end

section


/-!
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam


































end ThreeSumApsp.WordRam

end
end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The three source claims derived directly from the stronger Corollary 26 route.
These proofs avoid projecting from bundled claims that also prove unrelated
3SUM results and weaker bounds. The original source declarations are unchanged.
-/

namespace APSPFocusedSource

open ThreeSumApsp.WordRam


















end APSPFocusedSource





end



end


-- Original source module: ThreeSumApsp.RunningTimes.FromClaims.Bounds
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# From a realized running time to a program with the paper's bound

A claim gives a running time `T` with `T ≤ C X`, where `X` is the bound that the paper prints, and
`RealizedWithin` gives a program that takes `c T + c` steps.  This file puts the two together.

* Bounds in several parameters, valid on a domain on which `X ≥ 1`: `exists_solves`, and
  `exists_solves_nonneg` with `exists_solves_pair` for two programs with one slope and one constant.
* Bounds `O(n^a (log n)^e)` in one size, valid for all large `n`: `solvedAt_of_realized`, and for
  every exponent `κ` of the magnitude `solvedInTime_of_claim` and `solvedInPolylogTime_of_claim`.
* An instance with numbers bounded by `n^κ` is also one with numbers bounded by `n^κ'`, `κ ≤ κ'`
  (`solvedInTimeAt_mono`), so that a bound for all `κ ≥ 1` is a bound for all `κ`
  (`solvedInTime_of_one_le`).
-/

public section

namespace ThreeSumApsp.FromClaims

open ThreeSumApsp.WordRam
open EndStatement (Instr)

/-! ## Bounds on a domain -/











/-! ## Bounds in one size, for all large sizes -/



/-- A claim "solved in `O(n^a)` time on numbers of absolute value at most `n^κ`, for every `κ`", in
a reading `S` of "is solved in time T" that is realized, gives programs. -/
theorem solvedInTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {a : ℝ} (h : Claim.SolvedAlongPow S UpperBigOPow a) :
    SolvedInTime Q a 0 := by
  intro κ
  obtain ⟨T, hT, C, hb⟩ := h κ (Nat.cast_nonneg κ)
  exact solvedAt_of_realized T κ (hR T hT) (C := C)
    (by simpa only [pow_zero, mul_one] using hb)







end ThreeSumApsp.FromClaims

end
end


-- Original source module: ThreeSumApsp.RunningTimes.Sec3.Theorem22.MinPlusLayout
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The (min,+)-product: from a solver of the task to a program for the layout of the end statement

The (min,+)-product (Theorem 22).  `realized_minPlusProduct`: if the task `mpTask` is
solved in time T, then `EndStatement.MinPlusProduct` is solved on the word RAM within a constant
times T.

The input is n in cell 0, the first matrix from cell 1 and the second from cell 1 + n².  The product
goes to the n² cells from 1 + 2n², and the free pointer is 1 + 3n² (`minPlusInst`).  The input meets
the task's precondition (`pre_minPlusProduct`).  A solver leaves the list `minPlusList` in the
output cells, and each of its entries is a minimum as `EndStatement.MinPlusProduct` asks for: it is
attained, and it is a lower bound (`post_minPlusProduct`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec















/-- **The (min,+)-product**: if the task is solved in time T, then the product is computed on the
word RAM within a constant times T. -/
theorem realized_minPlusProduct (T : ℕ → ℝ → ℝ) (h : SolvedIn mpTask T) :
    Realized EndStatement.MinPlusProduct T :=
  wrapMinPlus.realized h

end Light.Sec3

end
end


-- Original source module: ThreeSumApsp.Util.Asymptotics.Powers
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Powers of `n` and of `log n` for large `n`

The facts behind the paper's `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`, for functions of a natural number
`n` and in the language of Mathlib's `f =O[atTop] g`. Powers of `n` are monotone in the exponent
(`isBigO_rpow_rpow_of_le`, `isBigO_rpow_mul_log_pow_of_le`) and multiply by adding exponents
(`rpow_mul_rpow_eventuallyEq`). A constant or a power of `log n` is below every positive power of
`n` (`eventually_le_rpow`, `isLittleO_log_pow_rpow`). Hence `n ^ a * (log n) ^ e` is `o(n ^ b)` and
`O(n ^ b)` for `a < b` (`isLittleO_rpow_mul_log_pow_rpow`, `isBigO_rpow_mul_log_pow_rpow`), which is
where logarithms are absorbed for large `n`; with the constant absorbed too, this is
`eventually_mul_rpow_mul_log_pow_le`. The rounded power `⌈n ^ μ⌉` tends to infinity for `μ > 0`
(`tendsto_ceil_rpow_atTop`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp



















/-- Logarithms are absorbed: `n ^ a * (log n) ^ e = O(n ^ b)` for `a < b`. -/
theorem isBigO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop] fun n : ℕ => (n : ℝ) ^ b :=
  (isLittleO_rpow_mul_log_pow_rpow hab e).isBigO





end ThreeSumApsp

end
end


-- Original source module: ThreeSumApsp.Util.Asymptotics.PowPolylog
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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









namespace IsBigOPow













/-- `O(n^a) · O(n^b) = O(n^(a+b))`. -/
protected theorem mul (hf : IsBigOPow f a) (hg : IsBigOPow g b) :
    IsBigOPow (fun n => f n * g n) (a + b) :=
  (IsBigO.mul hf hg).congr' EventuallyEq.rfl (rpow_mul_rpow_eventuallyEq a b)





/-- Constant factors are absorbed. -/
theorem const_mul (hf : IsBigOPow f a) (c : ℝ) : IsBigOPow (fun n => c * f n) a :=
  IsBigO.const_mul_left hf c







end IsBigOPow











/-! ### `Õ(n^a)` -/













namespace IsPowPolylog



























/-- Logarithms are absorbed: `Õ(n^a) ⊆ O(n^b)` for `a < b`. -/
theorem isBigOPow (hf : IsPowPolylog f a) (hab : a < b) : IsBigOPow f b := by
  obtain ⟨e, hf⟩ := hf
  exact hf.trans (isBigO_rpow_mul_log_pow_rpow hab e)



end IsPowPolylog



/-- Substituting a size: if `G(s) = O(s^a)` and `size n = O(n^μ)` with `a, μ ≥ 0`, then
`G(size n) = O(n^(a μ))`. The sizes need not tend to infinity. -/
protected theorem IsBigOPow.comp {G : ℕ → ℝ} {size : ℕ → ℕ} {μ : ℝ} (hG : IsBigOPow G a)
    (hsize : IsBigOPow (fun n => (size n : ℝ)) μ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) :
    IsBigOPow (fun n => G (size n)) (a * μ) := by
  have hmodel : IsBigOPow (fun n => (size n : ℝ) ^ a + 1) (a * μ) :=
    ((hsize.rpow ha).mono (mul_comm μ a).le).add ((isBigOPow_const 1).mono (mul_nonneg ha hμ))
  exact hmodel.of_isBigO
    (isBigO_comp_add_one hG (fun s => Real.rpow_nonneg s.cast_nonneg a) size)







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
  isPowLittleO_iff.2 fun η hη => (isPowLittleO_iff.1 hf η hη).const_mul c

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


-- Original source module: ThreeSumApsp.TimeClaims.Sec3.Definitions
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Running-time claims of Sections 2 to 4, for an abstract notion of "solved in time T"

The paper derives many of its running times from others: "Plug Theorem 19 into Theorem 21", "This is
Corollary 26 with N = n". To check such deductions on their own, this file introduces

* the record `DetTimeModel`: for each problem of Sections 2 to 4 a predicate on running times `T`,
  read as "a deterministic algorithm solves the problem in time `T`", about which nothing is
  assumed (the record `ConditionalTimes.TimeModel` of the three conditional lemmas is another
  one, and nothing links the two);
* two closure properties of the set of running times (namespace `Closure`), which are hypotheses
  like the claims;
* the claims, each as a proposition about `M : DetTimeModel` (namespace `Claim`): time sentences of
  the paper, transfer claims ("if B is solved in time T then A is solved in time extra + calls · T")
  that the paper proves or calls straightforward, and the results it cites from the literature
  (docstrings marked CITED, names starting with an author key, such as `Claim.CH20_Theorem_5_1`).

The lemmas of the files beside this one, such as `Corollary16.of_corollary_26`, are implications
between claims, valid for every `M`. No machine is defined here and no running time is proved here.
They are applied to the interpretation `Light.lightModel`, in which `M.problem T` says that a
procedure of a program of the light language solves the problem within `T` steps; there the lemmas
carry the running times of the programs to the theorems of the paper, and the compiler carries these
to the word RAM.  For that interpretation both closure properties and every claim, at the parameters
of the paper, are proved, the cited results included: the reductions are written as programs
(theorems named `claim_…` and `closure_…`), and the derived claims follow by the lemmas.  So no
statement about the word RAM has a claim as a hypothesis.

Conventions.

* The parameters of a running time.  Sizes (`n`, `N`, `s`) are exact.  `D` is exact for the matrix
  problems (the matrices are `N × D` and `D × N`); for the two triangle problems of Section 3.1 it
  is a declared parameter, given with the input: a graph whose middle part has at most `D` vertices.
  Only `w` and `u` are upper bounds: "at most `w` query pairs (or positions)", "numbers of absolute
  value at most `u`".
* Sizes are at least 1 and bounds `u` on numbers are at least 1.  The value of a running time at
  size 0 or at a bound below 1 has no meaning: `M.problem T` says nothing about it.
* Word length.  The intended machine is the paper's word RAM (Section 2); its words are taken to
  have `Θ(log(size))` bits, and `Θ(log(n + D))` bits for the four problems that have the parameter
  `D`.  Numbers need not fit into one word, since `u` is not bounded in terms of the size: a number
  of absolute value at most `u` takes at most about `1 + log u` words, whatever the size (sizes go
  down to 1), and about `κ` words if `u = n^κ`.  This is why factors `1 + log u` appear in
  overheads.  For `u = n^{O(1)}`, the case of the paper's theorems, these factors are constants or
  logarithms.
* Calls.  As in Section 3 of the paper ("the extra time plus the total time to solve B on each
  instance created"), a transfer claim charges a call of an algorithm exactly its running time, and
  everything else to the extra time.  An algorithm that is called runs on the caller's machine,
  whose words may be longer than its own input would require. Proving the claims for an
  interpretation `M` requires that this is legitimate for `M`.
* The bound `u` on the numbers is an argument of its own, not a function of the size, because
  Theorem 21(b) fixes the bound and lets the size vary.
* `O(·)` with several parameters is written with an explicit constant.  `O(·)` in `n` alone, along
  `u = n^κ`, is `UpperBigOPow`, `UpperPowPolylog` or `UpperPowLittleO`: a running time is only ever
  bounded from above.
-/

@[expose] public section

namespace ThreeSumApsp



/-! ## The bounds in `n`, `D` and the number `w` of positions or query pairs -/







namespace Closure





end Closure

namespace Claim

/-! ## Time sentences -/





/-! ## Transfer claims that the paper proves or calls straightforward -/











/-! ## Results cited from the literature, in the form needed for Theorem 21 -/









/-! ## Claims that are derived from the ones above -/























/-! ## Bounds in `n` alone, along `u = n^κ` -/





/-- 3SUM on `n` integers of absolute value at most `n^κ` is solved deterministically in
`n^{a+o(1)}` time, for every constant `κ ≥ 0`. -/
abbrev ThreeSumInLittleO (M : DetTimeModel) (a : ℝ) : Prop :=
  SolvedAlongPow M.threeSum UpperPowLittleO a





end Claim

end ThreeSumApsp

end
end


-- Original source module: ThreeSumApsp.TimeClaims.Sec3.Theorem21_22
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Running-time claims of Section 3.4: Theorems 21 and 22

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".  They
are deductions between running-time sentences: those of the paper for Theorem 22, and for
Theorem 21, which the paper cites, those of the route taken here.

* Theorem 21(a) from two reductions, [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]:
  `Theorem21a.of_CH20_VW13`.  The sizes, numbers of instances and extra times compose
  by the rules for `n^{a+o(1)}`.
* Theorem 21(b) for the (min,+)-product from [VW13, Theorem 3.3] and [VW18, Theorem 4.2]:
  `Theorem21b.minPlus_of_VW13_VW18`.  The time of the first reduction is again a good
  time (`GoodTime.mul_logU`), and `log (cU) = O(log U)` (`dominated_logU_mul`).
* Theorem 21(b) for APSP by repeated squaring: `Theorem21b.apsp_of_minPlus`, whose
  arithmetic is `dominated_repeatedSquaring`.
* "Plug Theorem 19 into Theorem 21": `threeSum_of_uniform_theorem_21a`,
  `minPlus_of_uniform_theorem_21b`, `apsp_of_uniform_theorem_21b`.
* Theorem 22: the roundings such as `n^{2-1/1296+o(1)} ≤ O(n^{1.99923})`
  (`Claim.SolvedAlongPow.mono`).
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Theorem 21(a) -/

/-- Theorem 21(a) from two reductions: [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]. -/
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

/-! ## Theorem 21(b): the (min,+)-product -/









/-! ## Theorem 21(b): APSP -/







/-! ## "Plug Theorem 19 into Theorem 21"

The time of Theorem 19 is `uniformTime K δ e s u = K s^{3-δ} (log s + 1)^e (1 + log u)²`.
Theorem 21 evaluates it at sizes `s(n)` and bounds `u(n) ≤ c n^κ` on the numbers, and multiplies it
by powers of `n` and logarithms.  So each bound is a product of functions of known classes. -/





/-- "Plug Theorem 19 into Theorem 21", 3SUM, in general form: with exponent `3 - δ` for Exact
Triangle the time for 3SUM is `n^{2-δ/2+o(1)}`. -/
theorem threeSum_of_uniform_theorem_21a (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21a M) :
    Claim.ThreeSumInLittleO M (2 - δ / 2) := by
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

/-- "Plug Theorem 19 into Theorem 21", (min,+)-product, in general form: with exponent `3 - δ` for
Exact Triangle the time is `O(n^{3-δ/3} (log n)^{O(1)})`. -/
theorem minPlus_of_uniform_theorem_21b (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21b_minPlus M) :
    Claim.MinPlusInPolylog M (3 - δ / 3) := by
  obtain ⟨K, hK, hex⟩ := hu
  obtain ⟨c, C, hc, h21⟩ := h21
  intro κ hκ
  obtain ⟨T', hT', hb⟩ := h21 _ (goodTime_uniformTime e hK hδ1) hex
  have hone : ∀ n : ℕ, 1 ≤ n → 1 ≤ (n : ℝ) ^ κ := fun n hn =>
    Real.one_le_rpow (Nat.one_le_cast.2 hn) hκ
  have htotal := ((((isBigOPow_natCast_pow 2).isPowPolylog.mul
    (isPowPolylog_uniformTime_cbrtCeil K (δ := δ) e (by linarith) hc hκ)).mul
    ((isPowPolylog_logU_of_le (c := 1) fun n hn => ⟨hone n hn, (one_mul _).ge⟩).pow 2)).const_mul
    C).mono (b := 3 - δ / 3) (le_of_eq (by push_cast; ring))
  exact ⟨T', hT', htotal.upperPowPolylog.mono_left
    (Filter.eventually_atTop.2 ⟨1, fun n hn => hb n _ hn (hone n hn)⟩)⟩



/-! ## Theorem 22 -/

/-- The roundings of Theorem 22, such as "n^{2-1/1296+o(1)} ≤ O(n^{1.99923})", at the level of
claims: an inclusion between two classes of running times carries over to the claims. -/
theorem Claim.SolvedAlongPow.mono {S : (ℕ → ℝ → ℝ) → Prop} {Cls Cls' : (ℕ → ℝ) → ℝ → Prop}
    {a b : ℝ} (h : Claim.SolvedAlongPow S Cls a) (hCls : ∀ f, Cls f a → Cls' f b) :
    Claim.SolvedAlongPow S Cls' b := fun κ hκ =>
  let ⟨T, hT, hb⟩ := h κ hκ
  ⟨T, hT, hCls _ hb⟩

end ThreeSumApsp

end
end


open ThreeSumApsp ThreeSumApsp.WordRam in
/-- Every rational exponent strictly above the unrounded 3SUM threshold is attained. -/
theorem solution (r : ℚ)
    (hr : (1.999125 : ℚ) < r) : EndStatement.ThreeSum.SolvedInTime r := by
  have hu := Light.Sec3.claim_exactTriangleUniform_usingCorollary26
  have h21 : Claim.Theorem_21a Light.lightModel :=
    Theorem21a.of_CH20_VW13 _ Light.Sec3.ChanHe.claim_CH20_Theorem_5_1
      Light.Sec3.claim_VW13_Theorem_4_3
  have hgap : (2 - (175e-5 : ℝ) / 2) < (r : ℝ) := by
    have hcast : ((1.999125 : ℚ) : ℝ) < (r : ℝ) := Rat.cast_lt.mpr hr
    norm_num at hcast ⊢
    exact hcast
  have h3 : SolvedInTime EndStatement.ThreeSum (r : ℝ) 0 :=
    FromClaims.solvedInTime_of_claim Light.Sec3.realized_threeSum
      ((threeSum_of_uniform_theorem_21a _ 1 (by norm_num) hu h21).mono
        fun _ hf => hf.upperBigOPow hgap)
  exact h3.endStatement rfl (by linarith)


#print axioms solution
