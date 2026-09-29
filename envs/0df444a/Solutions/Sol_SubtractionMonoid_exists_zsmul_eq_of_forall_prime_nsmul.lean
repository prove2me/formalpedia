-- Prove2me | solution 1 for SubtractionMonoid.exists_zsmul_eq_of_forall_prime_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/78f384e1-61fe-54eb-8a2e-6602041a1e4c

import Mathlib
import Theorems.Thm_SubtractionMonoid_exists_zsmul_eq_of_forall_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime_nsmul

set_option Elab.async false

theorem solution {A : Type*} [SubtractionMonoid A]
    (h : ∀ p : ℕ, p.Prime → ∀ x : A, ∃ y : A, p • y = x) :
    ∀ n : ℤ, n ≠ 0 → ∀ x : A, ∃ y : A, n • y = x :=
  SubtractionMonoid.exists_zsmul_eq_of_forall_prime (fun p hp x =>
    (h p hp x).imp fun y hy => by rw [natCast_zsmul]; exact hy)

#print axioms solution

end S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime_nsmul
end P2MW
export P2MW.S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime_nsmul (solution)
