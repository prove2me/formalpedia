-- Prove2me | solution 1 for Representation.trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ce480b97-fae6-5393-9cfd-9c10c38414a4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

theorem solution
    {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g u : G) (hgu : Commute g u) (a : ℕ) (hu : u ^ p ^ a = 1) :
    LinearMap.trace k V (ρ (g * u)) = LinearMap.trace k V (ρ g) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  ·
    have h : ρ (g * u) = ρ g := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [h]
  · haveI : CharP (Module.End k V) p :=
      charP_of_injective_algebraMap (algebraMap k (Module.End k V)).injective p

    set N : Module.End k V := ρ u - 1 with hN
    have hNp : N ^ p ^ a = 0 := by
      rw [hN, sub_pow_char_pow_of_commute p a (Commute.one_right _), one_pow, ← map_pow, hu,
        map_one, sub_self]
    have hNil : IsNilpotent N := ⟨p ^ a, hNp⟩

    have hcomm : Commute (ρ g) N := (hgu.map ρ).sub_right (Commute.one_right _)
    have hgN : IsNilpotent (ρ g * N) := hcomm.isNilpotent_mul_left hNil
    have htr : LinearMap.trace k V (ρ g * N) = 0 :=
      (LinearMap.isNilpotent_trace_of_isNilpotent hgN).eq_zero
    have hsplit : ρ (g * u) = ρ g + ρ g * N := by
      rw [map_mul, hN, mul_sub, mul_one, add_sub_cancel]
    rw [hsplit, map_add, htr, add_zero]

end S_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one
end P2MW
export P2MW.S_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one (solution)
