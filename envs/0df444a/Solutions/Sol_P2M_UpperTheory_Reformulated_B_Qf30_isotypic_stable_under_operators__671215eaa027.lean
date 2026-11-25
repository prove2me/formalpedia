-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qf30_isotypic_stable_under_operators__671215eaa027
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:45.099361+00:00
-- url     : https://prove2.me/submissions/51e8a1b8-d5a4-4a5a-b3c0-f48c0861de26

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsotypicStableUnderOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf30
theorem _root_.solution.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qf30.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V},
      x ∈ UpperTheory.Reformulated.B.Qf30.isoSub E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qf30.isoSub E mu := by
  intro n K V _ _ _ E mu a b x hx
  unfold UpperTheory.Reformulated.B.Qf30.isoSub at hx ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨u, hu, v, hv, rfl⟩
    refine Submodule.subset_span ⟨E a b * u, ?_, v, hv, rfl⟩
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ c hy
end UpperTheory.Reformulated.B.Qf30
