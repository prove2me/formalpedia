-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.physical_gap_of_mixed_energy
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:29:37.053644+00:00
-- url     : https://prove2.me/submissions/8d820234-54f4-4a91-aad8-1b1e323df2eb

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_physical_gap_of_native_source_bounds
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_mixed_diagonal_lower
import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
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
    (henergy : nativeLow*‖z 0‖^2-
      2*mixedUpper*(‖z 0‖*Real.sqrt (retainedEnergy z)) +
      retainedEnergy z + highFloor*‖h‖^2 ≤ energy) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤ energy := by
  apply physical_gap_of_native_source_bounds T x source hT hx hsource z h energy
  exact (add_le_add (mixed_diagonal_lower z) (le_refl _)).trans henergy
