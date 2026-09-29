-- Prove2me | solution 1 for Submodule.eq_span_singleton_of_card_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/836f8280-c518-5c6e-9826-141954eb120b

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_eq_span_singleton_of_card_eq_sq

theorem solution {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hV : Nat.card V = p ^ 2) (N : Submodule (ZMod p) V) (htop : N ≠ ⊤)
    {v : V} (hv : v ∈ N) (hv0 : v ≠ 0) : N = Submodule.span (ZMod p) {v} := by
  have hp : p.Prime := Fact.out
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; exact pow_ne_zero _ hp.ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite

  have h2 : Module.finrank (ZMod p) V = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm

  have hlt : Module.finrank (ZMod p) N < 2 := h2 ▸ Submodule.finrank_lt htop
  have hbot : N ≠ ⊥ := fun h => hv0 ((Submodule.mem_bot (R := ZMod p)).mp (h ▸ hv))
  have hpos : 0 < Module.finrank (ZMod p) N := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨v, hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have hN1 : Module.finrank (ZMod p) N = 1 := by omega

  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hv
  · rw [finrank_span_singleton hv0, hN1]

end S_Submodule_eq_span_singleton_of_card_eq_sq
end P2MW
export P2MW.S_Submodule_eq_span_singleton_of_card_eq_sq (solution)
