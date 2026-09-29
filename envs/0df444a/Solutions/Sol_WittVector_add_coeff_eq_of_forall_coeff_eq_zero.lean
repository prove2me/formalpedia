-- Prove2me | solution 1 for WittVector.add_coeff_eq_of_forall_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/12f3cac9-bda7-52ec-942a-2b28a356252e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_add_coeff_eq_of_forall_coeff_eq_zero

set_option autoImplicit false

universe u

theorem solution
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] (x y : WittVector p S) (r : ℕ)
    (hx : ∀ i : ℕ, i < r → x.coeff i = 0) :
    ∀ i : ℕ, i < r → (x + y).coeff i = y.coeff i := by
  intro i hi
  have hker : WittVector.truncate r x = 0 := (WittVector.mem_ker_truncate r x).2 hx
  have h := congrArg (fun t : TruncatedWittVector p r S => t.coeff ⟨i, hi⟩) (map_add (WittVector.truncate r) x y)
  simp only [hker, zero_add, WittVector.coeff_truncate] at h
  exact h

end S_WittVector_add_coeff_eq_of_forall_coeff_eq_zero
end P2MW
export P2MW.S_WittVector_add_coeff_eq_of_forall_coeff_eq_zero (solution)
