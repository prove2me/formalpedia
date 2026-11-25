-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qj11_aeval_mem_invariant_submodule__dd34f4fa0fb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:21.149171+00:00
-- url     : https://prove2.me/submissions/a808f00a-8b17-45a4-90ac-b2762aec4583

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AevalMemInvariantSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule
theorem _root_.solution.{u_1} :
    ∀ {Y : Type u_1} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y]
    (A : Module.End ℂ Y) (p : Submodule ℂ Y),
    (∀ y ∈ p, (A : Y → Y) y ∈ p) →
      ∀ (q : Polynomial ℂ), ∀ y ∈ p, ((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) q : Y → Y) y ∈ p := by
  intro Y _ _ A p hA q y hy
  have hpow : ∀ n : ℕ, (A ^ n) y ∈ p := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hA _ ih
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine p.sum_mem fun i _ => ?_
  rw [LinearMap.smul_apply]
  exact p.smul_mem _ (hpow i)
end UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule
