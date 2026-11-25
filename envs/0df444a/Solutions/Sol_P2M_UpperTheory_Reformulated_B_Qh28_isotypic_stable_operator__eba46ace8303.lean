-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qh28_isotypic_stable_operator__eba46ace8303
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:48.623658+00:00
-- url     : https://prove2.me/submissions/c8d4caee-4745-4094-9c7a-0cf6c347bca2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsotypicStableOperator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh28
theorem _root_.solution.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qh28.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) {x : V},
      x ∈ UpperTheory.Reformulated.B.Qh28.isoSub E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qh28.isoSub E mu := by
  intro n K V _ _ _ E mu a b x hx
  unfold UpperTheory.Reformulated.B.Qh28.isoSub at hx ⊢
  refine (Submodule.span_le (p := Submodule.comap (E a b) (Submodule.span K _))).2 ?_ hx
  rintro _ ⟨u, hu, v, hv, rfl⟩
  refine Submodule.subset_span ⟨E a b * u, ?_, v, hv, rfl⟩
  exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
end UpperTheory.Reformulated.B.Qh28
