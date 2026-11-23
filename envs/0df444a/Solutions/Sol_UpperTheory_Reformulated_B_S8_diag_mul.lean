-- Prove2me | solution 1 for UpperTheory.Reformulated.B.S8.diag_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:31.056371+00:00
-- url     : https://prove2.me/submissions/4bc2f386-53a0-435e-98a0-09582f206908

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.S8
namespace UpperTheory.Reformulated.B.S8
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hX : ∀ i j, j < i → X i j = 0)
    (hY : ∀ i j, j < i → Y i j = 0) (a : Fin n) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single_of_mem a (Finset.mem_univ a) ?_
  intro b _ hb
  rcases lt_or_gt_of_ne hb with h | h
  · rw [hX a b h, zero_mul]
  · rw [hY b a h, mul_zero]
end UpperTheory.Reformulated.B.S8
