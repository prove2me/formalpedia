-- Prove2me | solution 1 for TauCeti.tendsto_of_forall_eventually_lt_of_eventually_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:26:38.398909+00:00
-- url     : https://prove2.me/submissions/474ffe4b-2e36-44a8-ad8f-99a7976e9822

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A term-by-term lower bound, summed with an error budget

If every term of a family `a` is within `η'` below its counterpart in `d`, then summing over a
finite set accumulates that slack at most once per index, so the sum of `a` falls short of the sum
of `d` by at most `#s • η'`.

Stating the conclusion with an arbitrary `η` dominating `#s • η'`, rather than with `#s • η'`
itself, lets a caller fix an error budget first and choose `η'` afterwards — which is how the
bound is used when `η` is a prescribed `ε` and `η'` is solved for.

## Main results

* `Finset.sum_sub_le_sum_of_forall_sub_le`: the summed form of a term-by-term lower bound.
-/

 section

namespace Finset

/-- **A term-by-term lower bound, summed.** If every `a i` is within `η'` below `d i` on `s`, and
`η` dominates the accumulated slack `#s • η'`, then `∑ d - η ≤ ∑ a`.

Purely additive: no multiplication, no linearity and no strict monotonicity are used, so this
lives in an ordered additive group rather than an ordered ring. A caller working in a ring
rewrites the `nsmul` with `nsmul_eq_mul`. -/
theorem sum_sub_le_sum_of_forall_sub_le {ι M : Type*} [AddCommGroup M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {d a : ι → M} {η η' : M}
    (ha : ∀ i ∈ s, d i - η' ≤ a i) (hη : s.card • η' ≤ η) :
    (∑ i ∈ s, d i) - η ≤ ∑ i ∈ s, a i := by
  have hlb := Finset.sum_le_sum ha
  rw [Finset.sum_sub_distrib, Finset.sum_const] at hlb
  exact (sub_le_sub_left hη _).trans hlb

end Finset

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Lower bounds that saturate a limit of the sum are limits

Let `f i` be a finite family of functions into a linearly ordered field. If every `f i` is
eventually above each value below `c i`, so that `c i` is a lower bound for its lower limit, and
the sum `∑ i, f i` is eventually below each value above `∑ i, c i`, then every `f i` tends to
`c i`: the lower bounds of the other members leave room for no more than `c i` in the sum.

The two hypotheses are the two halves of `tendsto_order`, the lower half for each member and the
upper half for the sum. No boundedness is assumed, so the statement avoids the side conditions of
`Filter.liminf` and `Filter.limsup`.

This is how a one-sided estimate becomes an asymptotic: an argument that exhibits enough mass in
each member of a finite partition, and cannot see that there is no more, still determines every
member once the total is known.

The analogous Dirichlet-density squeeze is
`NumberField.Set.hasDirichletDensity_of_squeeze`.

## Main results

* `TauCeti.tendsto_of_forall_eventually_lt_of_eventually_sum_lt`: lower bounds on the members of
  a finite family whose sum is bounded above by the sum of the bounds are limits.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Filter Topology

/-- **Lower bounds that saturate the sum are limits.** Let `f i`, for `i ∈ s`, be functions into a
linearly ordered field with the order topology. If for every `i ∈ s` each value below `c i` is
eventually exceeded by `f i`, and each value above `∑ i ∈ s, c i` eventually exceeds
`∑ i ∈ s, f i`, then `f i₀` tends to `c i₀` for every `i₀ ∈ s`.

The hypotheses are the lower half of `tendsto_order` for each member and the upper half for the
sum; the upper half for a member is manufactured from the other members' lower bounds. -/
theorem solution {ι α 𝕜 : Type*} [_root_.Field 𝕜]
    [_root_.LinearOrder 𝕜] [_root_.IsStrictOrderedRing 𝕜] [_root_.TopologicalSpace 𝕜] [_root_.OrderTopology 𝕜]
    {l : _root_.Filter α} {s : _root_.Finset ι} {f : ι → α → 𝕜} {c : ι → 𝕜}
    (hlow : ∀ i ∈ s, ∀ b < c i, ∀ᶠ x in l, b < f i x)
    (hsum : ∀ b > ∑ i ∈ s, c i, ∀ᶠ x in l, ∑ i ∈ s, f i x < b) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    _root_.Filter.Tendsto (f i₀) l (𝓝 (c i₀)) := by
  classical
  refine _root_.tendsto_order.2 ⟨hlow i₀ hi₀, fun a ha ↦ ?_⟩
  -- Share the room `a - c i₀` between the sum and the `#s - 1` other members.
  set η := (a - c i₀) / s.card
  have hcard : (0 : 𝕜) < s.card := by exact_mod_cast Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have hη : 0 < η := _root_.div_pos (sub_pos.mpr ha) hcard
  have hoth : ∀ᶠ x in l, ∀ i ∈ s.erase i₀, c i - η < f i x :=
    (_root_.Filter.eventually_all_finset _).2 fun i hi ↦
      hlow i (_root_.Finset.mem_of_mem_erase hi) _ (_root_.sub_lt_self _ hη)
  filter_upwards [hsum _ (_root_.lt_add_of_pos_right _ hη), hoth] with x hx hx'
  have hrest := _root_.Finset.sum_sub_le_sum_of_forall_sub_le (fun i hi ↦ (hx' i hi).le) _root_.le_rfl
  rw [← _root_.Finset.add_sum_erase _ _ hi₀, ← _root_.Finset.add_sum_erase s c hi₀] at hx
  rw [_root_.nsmul_eq_mul, _root_.Finset.card_erase_of_mem hi₀,
    _root_.Nat.cast_pred (Finset.card_pos.mpr ⟨i₀, hi₀⟩)] at hrest
  -- The other members use up `(#s - 1) η` of the room and the sum the last `η`.
  have hηa : ((s.card : 𝕜) - 1) * η = a - c i₀ - η := by
    rw [_root_.sub_mul, _root_.mul_div_cancel₀ _ hcard.ne', _root_.one_mul]
  linarith

end TauCeti

end
end
