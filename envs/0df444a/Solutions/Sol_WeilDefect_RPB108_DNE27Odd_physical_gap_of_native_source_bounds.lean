-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.physical_gap_of_native_source_bounds
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:23:15.044615+00:00
-- url     : https://prove2.me/submissions/b4c8575c-461e-4f7f-8504-ea0c2eca827d

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_lower_pos
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_native_le_completed
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_source_square_certificate
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_denominator_guard
import Theorems.Thm_WeilDefect_RPB108_source_completed_columns_physical_gap
import Definitions.Def_RPB108_DNE27Numerics_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd
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
