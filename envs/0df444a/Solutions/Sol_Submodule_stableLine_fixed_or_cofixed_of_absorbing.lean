-- Prove2me | solution 1 for Submodule.stableLine_fixed_or_cofixed_of_absorbing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/60c92d95-a634-595b-8bce-b685eb0c752d

import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_stableLine_fixed_or_cofixed_of_absorbing

theorem solution {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hV : Nat.card V = p ^ 2) {G : Type*} [SMul G V] (S : Set G) (N : Submodule (ZMod p) V) (hN : ∀ g ∈ S, ∀ x ∈ N, g • x ∈ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤) (M : Submodule (ZMod p) V) (hM : M ≠ ⊤) (habs : ∀ g ∈ S, ∀ y : V, g • y - y ∈ M) : (∀ g ∈ S, ∀ x ∈ N, g • x = x) ∨ (∀ g ∈ S, ∀ y : V, g • y - y ∈ N) := by
  classical
  have hp : p.Prime := Fact.out

  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; exact pow_ne_zero _ hp.ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) V = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod, hV] at h
    exact (Nat.pow_right_injective hp.two_le h).symm

  have hN1 : Module.finrank (ZMod p) N = 1 := by
    have hlt : Module.finrank (ZMod p) N < Module.finrank (ZMod p) V :=
      Submodule.finrank_lt htop
    have hne : Module.finrank (ZMod p) N ≠ 0 := by
      rwa [Ne, Submodule.finrank_eq_zero]
    omega
  by_cases hle : N ≤ M
  ·
    right
    have hMlt : Module.finrank (ZMod p) M < Module.finrank (ZMod p) V :=
      Submodule.finrank_lt hM
    have hMN : N = M := Submodule.eq_of_le_of_finrank_le hle (by omega)
    intro g hg y
    rw [hMN]
    exact habs g hg y
  ·
    left
    have hinf : N ⊓ M = ⊥ := by
      by_contra hne
      have hne' : Module.finrank (ZMod p) ↥(N ⊓ M) ≠ 0 := by
        rwa [Ne, Submodule.finrank_eq_zero]
      have heq : N ⊓ M = N :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      exact hle (heq ▸ inf_le_right)
    intro g hg x hx
    have hmem : g • x - x ∈ N ⊓ M := ⟨N.sub_mem (hN g hg x hx) hx, habs g hg x⟩
    rw [hinf, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem

end S_Submodule_stableLine_fixed_or_cofixed_of_absorbing
end P2MW
export P2MW.S_Submodule_stableLine_fixed_or_cofixed_of_absorbing (solution)
