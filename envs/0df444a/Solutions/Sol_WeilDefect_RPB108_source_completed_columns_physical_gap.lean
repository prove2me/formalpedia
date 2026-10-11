-- Prove2me | solution 1 for WeilDefect.RPB108.source_completed_columns_physical_gap
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:18:13.094915+00:00
-- url     : https://prove2.me/submissions/08056ced-a550-496d-a8d4-9bfa5448f555

import Theorems.Thm_WeilDefect_RPB108_completed_column_norm_le
import Theorems.Thm_WeilDefect_RPB108_completed_columns_physical_gap
import Mathlib
open scoped BigOperators
set_option autoImplicit false
open WeilDefect.RPB108
theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x source : Fin 4 → E)
    (m q B L : Fin 4 → ℝ) (k gap : ℝ)
    (hk : 0 < k) (hT : ‖T‖ ≤ 1/k)
    (hx : ∀ i, ‖x i‖ ≤ m i) (hsource : ∀ i, ‖source i‖^2 ≤ q i)
    (hm : ∀ i, m i ≤ B i) (hq : ∀ i, q i ≤ (k*(B i-m i))^2)
    (hL : ∀ i, 0 < L i) (hgap : 0 ≤ gap)
    (hbound : gap * ((∑ i, (B i)^2/L i) + 1/k) ≤ 1)
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ)
    (henergy : (∑ i, L i * ‖z i‖^2) + k*‖h‖^2 ≤ energy) :
    gap * ‖(∑ i, z i • (x i-T (source i))) + h‖^2 ≤ energy := by
  apply completed_columns_physical_gap (fun i => x i-T (source i)) B L k gap
    (fun i => completed_column_norm_le T (x i) (source i) (m i) (q i) k (B i)
      hk hT (hx i) (hsource i) (hm i) (hq i)) hL hk hgap hbound z h energy henergy
