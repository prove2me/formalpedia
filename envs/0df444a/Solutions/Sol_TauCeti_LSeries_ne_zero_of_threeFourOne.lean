-- Prove2me | solution 1 for TauCeti.LSeries.ne_zero_of_threeFourOne
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:07.50117+00:00
-- url     : https://prove2.me/submissions/afe0d0ef-5124-4954-bd29-e5814be764fb

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Nonvanishing on the line `Re s = 1` from a 3-4-1 bound

The classical `3-4-1` argument proves that an `L`-series does not vanish on the line `Re s = 1`
in two steps. The first is arithmetic: an Euler product and the positivity of
`3 + 4 cos θ + cos 2θ` give, for real `σ > 1`,

```text
1 ≤ ‖L₀(σ) ^ 3 * L₁(σ + it) ^ 4 * L₂(σ + 2it)‖,
```

where `L₀` is the series of the trivial character, `L₁` that of a character `χ`, and `L₂` that of
`χ²`. The second step is analytic and uses no arithmetic: if `L₀(σ) = O((σ - 1)⁻¹)` as `σ → 1⁺`,
`L₂` stays bounded near `1 + 2it`, and `L₁` is differentiable at `1 + it` and vanishes there,
then as `σ → 1⁺` the product is `O((σ - 1)⁻³ (σ - 1)⁴) = O(σ - 1)`, contradicting the
lower bound. This file proves the second step for arbitrary functions, so that each family of
`L`-series needs to supply only its own `3-4-1` bound and its analytic inputs.

The growth condition on `f₀` is the one-sided bound `f₀(σ) = O((σ - 1)⁻¹)` as real `σ → 1⁺`.
It follows from a limit of `(σ - 1) f₀(σ)` as `σ → 1⁺`, which is how such a bound is usually
available for a Dedekind zeta function; `TauCeti.isBigO_inv_sub_one_of_tendsto_sub_one_mul`
records that implication.

## Main results

* `TauCeti.LSeries.ne_zero_of_threeFourOne`: the `3-4-1` bound together with the bound
  `f₀(σ) = O((σ - 1)⁻¹)`, differentiability of `f₁` at `1 + it` and continuity of `f₂` at
  `1 + 2it` forces `f₁ (1 + it) ≠ 0`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The argument is the one in Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by
  Michael Stoll and David Loeffler, where the private lemma
  `DirichletCharacter.LFunction_ne_zero_of_not_quadratic_or_ne_one` carries it out for Dirichlet
  `L`-functions. Here it is separated from the Dirichlet characters.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Asymptotics Complex Filter
open scoped Topology

/-- **The `3-4-1` nonvanishing criterion.** Let `f₀`, `f₁`, `f₂` be complex functions and `t` real.
Suppose that, as `σ → 1⁺` through real values,

* `1 ≤ ‖f₀(σ) ^ 3 * f₁(σ + it) ^ 4 * f₂(σ + 2it)‖` eventually;
* `f₀(σ) = O((σ - 1)⁻¹)`;

and that `f₁` is complex differentiable at `1 + it` and `f₂` is continuous at `1 + 2it`. Then
`f₁ (1 + it) ≠ 0`.

The bound is the one an Euler product and `3 + 4 cos θ + cos 2θ ≥ 0` give when `f₀`, `f₁`, `f₂` are
the series of the trivial character, of a character `χ`, and of `χ²`; the analytic hypotheses are
where a continuation of these series across `Re s = 1` is used. -/
theorem solution {f₀ f₁ f₂ : ℂ → ℂ} {t : ℝ}
    (hbound : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      1 ≤ ‖f₀ σ ^ 3 * f₁ (σ + _root_.Complex.I * t) ^ 4 * f₂ (σ + 2 * _root_.Complex.I * t)‖)
    (h₀ : (fun σ : ℝ ↦ f₀ σ) =O[𝓝[>] 1] fun σ : ℝ ↦ (σ - 1)⁻¹)
    (h₁ : _root_.DifferentiableAt ℂ f₁ (1 + _root_.Complex.I * t)) (h₂ : _root_.ContinuousAt f₂ (1 + 2 * _root_.Complex.I * t)) :
    f₁ (1 + _root_.Complex.I * t) ≠ 0 := by
  intro hz
  -- The horizontal line `σ ↦ σ + c` through `c + 1` tends to `c + 1` as `σ → 1⁺`.
  have hline (c : ℂ) : _root_.Filter.Tendsto (fun σ : ℝ ↦ (σ : ℂ) + c) (𝓝[>] 1) (𝓝 (1 + c)) := by
    refine _root_.tendsto_nhdsWithin_of_tendsto_nhds ?_
    exact (continuous_ofReal.add _root_.continuous_const).tendsto' (1 : ℝ) (1 + c) (by simp)
  -- Since `f₁` vanishes at `1 + it`, it is `O(σ - 1)` along the horizontal line.
  have H₁ : (fun σ : ℝ ↦ f₁ (σ + _root_.Complex.I * t)) =O[𝓝[>] 1] fun σ : ℝ ↦ σ - 1 := by
    have := h₁.isBigO_sub.comp_tendsto (hline (_root_.Complex.I * t))
    simp only [_root_.Function.comp_def, hz, _root_.sub_zero, _root_.add_sub_add_right_eq_sub] at this
    exact this.trans (_root_.Asymptotics.isBigO_of_le _ fun σ ↦ by rw [← _root_.Complex.ofReal_one, ← _root_.Complex.ofReal_sub, _root_.Complex.norm_real])
  have H₂ : (fun σ : ℝ ↦ f₂ (σ + 2 * _root_.Complex.I * t)) =O[𝓝[>] 1] fun _ : ℝ ↦ (1 : ℝ) := by
    have := h₂.tendsto.comp (hline (2 * _root_.Complex.I * t))
    simp only [_root_.Function.comp_def] at this
    exact this.isBigO_one ℝ
  -- Hence the product is `O((σ - 1)⁻³ (σ - 1)⁴) = O(σ - 1)`, which tends to `0`.
  have H : (fun σ : ℝ ↦ f₀ σ ^ 3 * f₁ (σ + _root_.Complex.I * t) ^ 4 * f₂ (σ + 2 * _root_.Complex.I * t)) =o[𝓝[>] 1]
      fun _ : ℝ ↦ (1 : ℝ) := by
    have hlin : (fun σ : ℝ ↦ σ - 1) =o[𝓝[>] 1] fun _ : ℝ ↦ (1 : ℝ) :=
      (_root_.Asymptotics.isLittleO_one_iff ℝ).mpr <| _root_.tendsto_nhdsWithin_of_tendsto_nhds <|
        (continuous_id.sub _root_.continuous_const).tendsto' (1 : ℝ) 0 (_root_.sub_self 1)
    refine (((h₀.pow 3).mul (H₁.pow 4)).mul H₂).trans_isLittleO (hlin.congr' ?_ .rfl)
    filter_upwards [_root_.self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    have : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
    field_simp
  -- But the product is bounded below by `1`, so `1 = o(1)`, which is absurd.
  exact _root_.Asymptotics.isLittleO_irrefl (.of_forall fun _ ↦ _root_.one_ne_zero) <|
    (_root_.Asymptotics.IsBigO.of_bound' (by simpa using hbound)).trans_isLittleO H

end TauCeti.LSeries

end
end
