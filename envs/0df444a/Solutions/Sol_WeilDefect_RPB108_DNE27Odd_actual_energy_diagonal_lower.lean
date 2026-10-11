-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.actual_energy_diagonal_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:03:46.048144+00:00
-- url     : https://prove2.me/submissions/361a9142-9a6d-4b47-a116-0726ed191b27

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_combined_mixed_norm_bound
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_lowLower_identity
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_mixed_root_certificate
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_retained_energy_nonneg
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_theta_bounds
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_threeLower_identity
import Theorems.Thm_WeilDefect_RPB108_mixed_pairing_norm_le
import Theorems.Thm_WeilDefect_RPB108_paid_actual_energy_lower
import Mathlib
import Definitions.Def_RPB108_ThreeGram
import Definitions.Def_RPB108_DNE27Gram_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem solution (z : Fin 4 → ℂ) (Venergy : ℝ) (p q : ℂ)
    (hv : retainedEnergy z ≤ Venergy)
    (hp : ‖p‖^2 ≤ nativeDualSquare*Venergy)
    (hq : ‖q‖^2 ≤ highMixedSquare*Venergy) :
    (∑ i, lower i*‖z i‖^2) ≤
      nativeLow*‖z 0‖^2-2*‖z 0‖*‖p-q‖+Venergy := by
  have hV := (retained_energy_nonneg z).trans hv
  obtain ⟨ha,hb,_,_,_⟩ := mixed_root_certificate
  have hm := mixed_pairing_norm_le p q _ _ _ _ ha hb hV hp hq
    combined_mixed_norm_bound
  have hy := paid_actual_energy_lower nativeLow mixedUpper theta ‖z 0‖
    Venergy (retainedEnergy z) p q theta_bounds.1.le theta_bounds.2
    (norm_nonneg _) hV hv hm
  rw [← lowLower_identity] at hy
  have hs : (∑ i, lower i*‖z i‖^2) = lowLower*‖z 0‖^2+theta*retainedEnergy z := by
    simp [lower, retainedEnergy, Fin.sum_univ_succ, threeLower_identity]
    ring
  exact hs.trans_le hy
