-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qe29_isotypic_stable_gl_operator__5e779e4dc8f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:43.720891+00:00
-- url     : https://prove2.me/submissions/9d3d6fcd-f5d8-4368-ba9a-153569d2949a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsotypicStableGlOperator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qe29
theorem _root_.solution.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qe29.GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n),
      ∀ x ∈ UpperTheory.Reformulated.B.Qe29.isoSub E mu, (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qe29.isoSub E mu := by
  intro n K V _ _ _ E mu a b x hx
  have hE : E a b ∈ UpperTheory.Reformulated.B.Qe29.Umon E := Submonoid.subset_closure ⟨(a, b), rfl⟩
  have hle : UpperTheory.Reformulated.B.Qe29.isoSub E mu ≤ (UpperTheory.Reformulated.B.Qe29.isoSub E mu).comap (E a b) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, v, hv, rfl⟩
    exact Submodule.subset_span ⟨E a b * u, Submonoid.mul_mem _ hE hu, v, hv, rfl⟩
  exact hle hx
end UpperTheory.Reformulated.B.Qe29
