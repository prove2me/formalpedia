-- Prove2me | solution 1 for TauCeti.summable_mul_norm_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:29.383482+00:00
-- url     : https://prove2.me/submissions/eebc6c31-d9b4-43f5-a42f-31f29719f035

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Weighted geometric majorants over an index and an exponent

For a family `r : ι → E` in a seminormed additive group whose norms are less than one, and
eventually at most `1 - ε`, wherever the weight `w` is nonzero, the double family
`(i, e) ↦ w i * ‖r i‖ ^ (e + 1)` is summable over `ι × ℕ` as soon as `i ↦ w i * ‖r i‖` is
summable. Each fibre is geometric, so it
sums to `w i * ‖r i‖ / (1 - ‖r i‖)`, and the eventual bound keeps `1 / (1 - ‖r i‖)` under `ε⁻¹`
off a finite set; a fibre where the weight vanishes is zero and needs no bound at all.

## Main results

* `TauCeti.summable_mul_norm_pow_succ`: the weighted double family is summable over `ι × ℕ`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

/-- **A weighted geometric family is summable over index and exponent together.**  Let `w : ι → ℝ`
be weights with `i ↦ w i * ‖r i‖` summable, and let `r` be a family in a seminormed additive group
which, *at every index where `w` is nonzero*, has norm less than one and eventually norm at most
`1 - ε`.  Then the double family `(i, e) ↦ w i * ‖r i‖ ^ (e + 1)` is summable over `ι × ℕ`.

Both conditions on `r` are restricted to the support of `w`, and off that support nothing is asked
of `r` at all: a fibre with `w i = 0` is identically zero whatever `r i` is.  The weights are
unrestricted in sign, since only `|w i|` enters the majorant.

The eventual bound is what the fibres need — the fibre at `i` sums to `w i * ‖r i‖ / (1 - ‖r i‖)`,
which is comparable to `w i * ‖r i‖` only where `‖r i‖` stays away from `1`. Summability of `r`
would give this, but is far stronger: it rules out a family of constant norm with summable
weights.

This is the bound a termwise differentiation argument runs on whenever the differentiated terms are
an index-only weight times a norm power; it says nothing on its own about which families have that
form. -/
theorem solution {ι E : Type*} [_root_.SeminormedAddGroup E] {r : ι → E} {w : ι → ℝ}
    (hbd : ∃ ε > 0, ∀ᶠ i in _root_.Filter.cofinite, w i ≠ 0 → ‖r i‖ ≤ 1 - ε)
    (hwr : _root_.Summable fun i ↦ w i * ‖r i‖) (h1 : ∀ i, w i ≠ 0 → ‖r i‖ < 1) :
    _root_.Summable fun ie : ι × ℕ ↦ w ie.1 * ‖r ie.1‖ ^ (ie.2 + 1) := by
  obtain ⟨ε, hε, hfar⟩ := hbd
  have habs : _root_.Summable fun i ↦ |w i| * ‖r i‖ := by
    refine (_root_.summable_abs_iff.2 hwr).congr fun i ↦ ?_
    rw [_root_.abs_mul, _root_.abs_of_nonneg (_root_.norm_nonneg (r i))]
  -- The absolute-value family is nonnegative, so it can be assembled fibrewise.  A fibre with
  -- `w i = 0` is identically zero, so it needs no hypothesis on `‖r i‖`.
  have hfib : ∀ i, _root_.Summable fun e : ℕ ↦ |w i| * ‖r i‖ ^ (e + 1) := fun i ↦ by
    rcases _root_.eq_or_ne (w i) 0 with h | h
    · simp [h]
    · exact (((_root_.summable_geometric_of_lt_one (_root_.norm_nonneg _) (h1 i h)).mul_left ‖r i‖).congr
        fun e ↦ by ring).mul_left |w i|
  have houter : _root_.Summable fun i ↦ ∑' e : ℕ, |w i| * ‖r i‖ ^ (e + 1) := by
    refine _root_.Summable.of_norm_bounded_eventually (g := fun i ↦ ε⁻¹ * (|w i| * ‖r i‖))
      (habs.mul_left ε⁻¹) ?_
    filter_upwards [hfar] with i hi
    rcases _root_.eq_or_ne (w i) 0 with h | h
    · simp [h]
    · have hval : ∑' e : ℕ, |w i| * ‖r i‖ ^ (e + 1) = |w i| * (‖r i‖ / (1 - ‖r i‖)) := by
        rw [_root_.tsum_mul_left, _root_.tsum_congr fun e ↦ _root_.pow_succ' ‖r i‖ e, _root_.tsum_mul_left,
          _root_.tsum_geometric_of_lt_one (_root_.norm_nonneg _) (h1 i h), _root_.div_eq_mul_inv]
      rw [_root_.Real.norm_of_nonneg (_root_.tsum_nonneg fun e ↦ by positivity), hval]
      -- Where `‖r i‖ ≤ 1 - ε` the fibre sum `‖r i‖ / (1 - ‖r i‖)` is at most `ε⁻¹ ‖r i‖`.
      have hd : ‖r i‖ / (1 - ‖r i‖) ≤ ε⁻¹ * ‖r i‖ := by
        rw [_root_.div_le_iff₀ (by linarith [h1 i h])]
        have hεi : ε * (ε⁻¹ * ‖r i‖) = ‖r i‖ := by field_simp
        nlinarith [_root_.norm_nonneg (r i), _root_.inv_pos.2 hε, hi h]
      calc |w i| * (‖r i‖ / (1 - ‖r i‖)) ≤ |w i| * (ε⁻¹ * ‖r i‖) :=
            _root_.mul_le_mul_of_nonneg_left hd (_root_.abs_nonneg _)
        _ = ε⁻¹ * (|w i| * ‖r i‖) := by ring
  have hmaj : _root_.Summable fun ie : ι × ℕ ↦ |w ie.1| * ‖r ie.1‖ ^ (ie.2 + 1) :=
    (_root_.summable_prod_of_nonneg fun ie ↦ by positivity).mpr ⟨hfib, houter⟩
  refine hmaj.of_norm_bounded fun ie ↦ ?_
  rw [_root_.Real.norm_eq_abs, _root_.abs_mul,
    _root_.abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖r ie.1‖ ^ (ie.2 + 1))]

end TauCeti

end
end
