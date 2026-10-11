-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.physical_gap_of_native_source_bounds
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:20:41.649824+00:00
-- url     : https://prove2.me/submissions/7b27256f-f0d9-4a13-84c2-7abf9afdf215

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_lower_pos
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_native_le_completed
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_source_square_certificate
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_denominator_guard
import Theorems.Thm_WeilDefect_RPB108_source_completed_columns_physical_gap
import Definitions.Def_RPB108_DNE27Numerics_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x source : Fin 4 → E)
    (hT : ‖T‖ ≤ 1/highFloor)
    (hx : ∀ i, ‖x i‖ ≤ nativeMass i)
    (hsource : ∀ i, ‖source i‖^2 ≤ sourceSquare i)
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ)
    (henergy : (∑ i, lower i * ‖z i‖^2) + highFloor*‖h‖^2 ≤ energy) :
    (4/(10^36) : ℝ) * ‖(∑ i, z i • (x i-T (source i))) + h‖^2 ≤ energy := by
  exact source_completed_columns_physical_gap T x source nativeMass sourceSquare
    completedMass lower highFloor gap (by norm_num [highFloor]) hT hx hsource
    native_le_completed source_square_certificate lower_pos (by norm_num [gap])
    denominator_guard z h energy henergy
