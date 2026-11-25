-- Prove2me | solution 1 for P2M_GlobalTheory_matrix_stableRange_one__75f66df7c4ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:24.162237+00:00
-- url     : https://prove2.me/submissions/0efaeefc-18e4-45d9-be4d-669e63b6e888

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixFieldStableRangeOneDetNeZero
import Theorems.Thm_GlobalTheory_matrix_stableRange_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (κ : Type) [Field κ] (n : ℕ) (c d p q : Matrix (Fin n) (Fin n) κ),
    c * p + d * q = 1 → ∃ y : Matrix (Fin n) (Fin n) κ, (c * y + d).det ≠ 0 :=
  fun κ _ n c d p q h => matrix_stableRange_one κ n c d p q h
end GlobalTheory
