-- Prove2me | solution 1 for UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:05.820492+00:00
-- url     : https://prove2.me/submissions/0efd977c-fe10-4f77-a4b6-c0d34cd75dac

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryGroupStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem
theorem _root_.solution :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {j k : ℕ}
      {x y : Module.End ℂ V},
      x ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j → y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k → x * y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
  intro n V _ _ E j k x y hx hy
  have h : UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j * UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k ≤ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
    unfold UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro z ⟨a, ⟨l1, hl1, rfl⟩, b, ⟨l2, hl2, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨l1 ++ l2, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · simp [List.map_append, List.prod_append]
  exact h (Submodule.mul_mem_mul hx hy)
end UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem
