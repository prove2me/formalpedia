-- Prove2me | solution 1 for QnAudit.oldQ_pos
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:10:06.78641+00:00
-- url     : https://prove2.me/submissions/2f56955f-9657-4c7a-9766-230ab72c10a5

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_moment_pos
open MeasureTheory Set
open QnAudit

theorem solution (K : ℝ → ℝ) (u : ℝ) (n : ℕ)
    (hu : 0 < u) (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight (u ^ 2) n t * K t) (Ioi 0)) :
    0 < oldQ K u n := by
  exact mul_pos (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _) (pow_pos hu _))
    (moment_pos K (u ^ 2) n hK hi)
