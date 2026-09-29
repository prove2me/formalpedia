-- Prove2me | solution 1 for ZMod.natCard_dvd_of_forall_pow_eq_one_units_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e101db42-3598-594c-a8c7-18d573f81c58

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow
set_option autoImplicit false

theorem solution
    (p : ℕ) (hp : p.Prime) (q : ℕ) (hq : q ≠ 0)
    (H : Subgroup (ZMod (p ^ (padicValNat p q + 1)))ˣ) (hH : ∀ x ∈ H, x ^ q = 1) :
    Nat.card H ∣ q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ (padicValNat p q + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hexp : Monoid.exponent H ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => Subtype.ext (by
      have := hH g.1 g.2; simpa using this))
  by_cases hp2 : p = 2
  · subst hp2
    have hcardU : Nat.card (ZMod (2 ^ (padicValNat 2 q + 1)))ˣ = 2 ^ padicValNat 2 q := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos _)]
      simp
    refine (Subgroup.card_subgroup_dvd_card H).trans ?_
    rw [hcardU]
    exact pow_padicValNat_dvd
  · haveI : IsCyclic (ZMod (p ^ (padicValNat p q + 1)))ˣ :=
      ZMod.isCyclic_units_of_prime_pow p hp hp2 _
    haveI : IsCyclic H := Subgroup.isCyclic H
    rw [← IsCyclic.exponent_eq_card]
    exact hexp

end S_ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow
end P2MW
export P2MW.S_ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow (solution)
