-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qj21.ms_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:30.543801+00:00
-- url     : https://prove2.me/submissions/e0373fdb-7141-4591-8919-5ef28ac014d7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MsMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qj21
theorem _root_.solution :
    ∀ {H : Type} {N0 N1 : ℕ} (t : H) {a b a' b' : ℕ} {P Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1},
      P ∈ UpperTheory.Reformulated.B.Qj21.MS t a b → Q ∈ UpperTheory.Reformulated.B.Qj21.MS t a' b' → P * Q ∈ UpperTheory.Reformulated.B.Qj21.MS t (a + a') (b + b') := by
  intro H N0 N1 t a b a' b' P Q hP hQ
  have key : UpperTheory.Reformulated.B.Qj21.MS (N0 := N0) (N1 := N1) t a b * UpperTheory.Reformulated.B.Qj21.MS t a' b'
      ≤ UpperTheory.Reformulated.B.Qj21.MS t (a + a') (b + b') := by
    unfold UpperTheory.Reformulated.B.Qj21.MS
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨x, ⟨L, rfl, h1, h2⟩, y, ⟨L', rfl, h3, h4⟩, rfl⟩
    refine ⟨L ++ L', ?_, ?_, ?_⟩
    · simp only [UpperTheory.Reformulated.B.Qj21.tmL, List.map_append, List.prod_append, mul_one]
    · rw [← h1, ← h3]
      simp only [UpperTheory.Reformulated.B.Qj21.nzc, List.map_append, List.sum_append]
    · rw [← h2, ← h4]
      simp only [UpperTheory.Reformulated.B.Qj21.z0c, List.map_append, List.sum_append]
  exact key (Submodule.mul_mem_mul hP hQ)
end UpperTheory.Reformulated.B.Qj21
