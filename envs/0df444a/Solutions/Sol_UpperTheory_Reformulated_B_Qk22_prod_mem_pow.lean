-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk22.prod_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:44.257245+00:00
-- url     : https://prove2.me/submissions/3da621da-cbe0-47ee-a6ec-b3f89e6018fc

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProdMemPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk22
theorem _root_.solution :
    ∀ {R k : Type} [inst : CommRing R] [inst_1 : CommRing k]
    [inst_2 : Algebra R k] (J : Submodule R k) {β : Type} (t : Finset β) (x : β → k) (e : β → ℕ),
    (∀ b ∈ t, x b ∈ J ^ e b) → ∏ b ∈ t, x b ∈ J ^ ∑ b ∈ t, e b := by
  intro R k _ _ _ J β t x e h
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, pow_zero]
    exact Submodule.one_le.mp le_rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
    exact Submodule.mul_mem_mul (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
end UpperTheory.Reformulated.B.Qk22
