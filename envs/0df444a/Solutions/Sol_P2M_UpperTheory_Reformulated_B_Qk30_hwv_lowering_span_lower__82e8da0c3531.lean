-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qk30_hwv_lowering_span_lower__82e8da0c3531
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:58.362117+00:00
-- url     : https://prove2.me/submissions/686fa730-5808-4899-9f17-bced4f62215d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HwvLoweringSpanLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk30
theorem _root_.solution.{u_1, u_2} :
    ∀ {n : ℕ} {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
      (E : UpperTheory.Reformulated.B.Qk30.GLOps n K V) (mu : Fin n → ℤ) {a b : Fin n},
      b < a → ∀ {x : V}, x ∈ UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan E mu → (E a b : V → V) x ∈ UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan E mu := by
  intro n K V _ _ _ E mu a b hab x hx
  unfold UpperTheory.Reformulated.B.Qk30.hwvLoweringSpan at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    refine Submodule.subset_span ⟨E a b * u, ?_, w, hw, rfl⟩
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨a, b, hab, rfl⟩) hu
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy
end UpperTheory.Reformulated.B.Qk30
