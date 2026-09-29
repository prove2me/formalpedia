-- Prove2me | solution 1 for WittVector.ringHom_ext_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a06fcd4e-7f0e-5381-bd82-f8f530de5b95

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_ringHom_ext_padicInt

set_option autoImplicit false

open scoped PadicInt

universe u

namespace Ws23RingHomExt

theorem ringHom_padicInt_wittVector_eq (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
    (f g : ℤ_[p] →+* WittVector p R) : f = g := by
  refine RingHom.ext fun x => ?_
  rw [← sub_eq_zero]
  ext m

  obtain ⟨y, hy⟩ : ∃ y : ℤ_[p], y * (p : ℤ_[p]) ^ (m + 1) = x - (x.appr (m + 1) : ℤ_[p]) :=
    Ideal.mem_span_singleton'.mp (PadicInt.appr_spec (m + 1) x)
  have hx : x = (x.appr (m + 1) : ℤ_[p]) + y * (p : ℤ_[p]) ^ (m + 1) := by rw [hy]; ring

  have : f x - g x = (f y - g y) * (p : WittVector p R) ^ (m + 1) := by
    rw [hx, map_add, map_add, map_natCast, map_natCast, map_mul, map_mul, map_pow, map_pow, map_natCast,
      map_natCast]
    ring

  rw [this, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m), WittVector.zero_coeff]

end Ws23RingHomExt

theorem solution
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]
    (f g : ℤ_[p] →+* WittVector p R) : f = g :=
  Ws23RingHomExt.ringHom_padicInt_wittVector_eq p f g

end S_WittVector_ringHom_ext_padicInt
end P2MW
export P2MW.S_WittVector_ringHom_ext_padicInt (solution)
