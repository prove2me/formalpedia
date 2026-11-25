-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qn11.derivation_mem_pow_of_mem_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:51:21.031242+00:00
-- url     : https://prove2.me/submissions/5bd49455-f7f6-4fab-8ba7-35b64426bc00

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerivationMemPowOfMemPowSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qn11
theorem _root_.solution :
    ∀ {R : Type} [inst : CommRing R]
    (I : Ideal R) (D : Derivation ℤ R R) {n : ℕ} {r : R}, r ∈ I ^ (n + (1 : ℕ)) → (D : R → R) r ∈ I ^ n := by
  intro R _ I D n
  induction n with
  | zero =>
    intro r _
    simp
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ, mul_comm b]
      exact Ideal.mul_mem_mul (ih ha) hb
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy
end UpperTheory.Reformulated.B.Qn11
