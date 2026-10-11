-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.physical_gap_of_gram_and_pairings
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:09:08.922698+00:00
-- url     : https://prove2.me/submissions/dfee9148-16bf-4b15-8476-41f60e4265fd

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_actual_energy_diagonal_lower
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_physical_gap_of_native_source_bounds
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_source_gram_domination
import Theorems.Thm_WeilDefect_RPB108_scaled_gram_difference
import Theorems.Thm_WeilDefect_RPB108_source_cross_square_of_gram_domination
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108.DNE27Even
theorem row_margin_certificate (i : Fin 3) :
    rowMargins diagonalLower offBounds i = publishedMargins i ∧
    0 < publishedMargins i := by
  fin_cases i <;> norm_num [rowMargins, diagonalLower, scaledLower,
    gramScales, scales, Matrix.cons_val_two, rho, nativeLower, gramUpper, offBounds, publishedMargins]
end WeilDefect.RPB108.DNE27Even

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x source : Fin 4 → E)
    (hT : ‖T‖ ≤ 1/highFloor)
    (hx : ∀ i, ‖x i‖ ≤ nativeMass i)
    (hsource : ∀ i, ‖source i‖^2 ≤ sourceSquare i)
    (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ) (p q : ℂ)
    (hv : retainedEnergy z ≤ complexGram V
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hp : ‖p‖^2 ≤ nativeDualSquare*complexGram V
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hq : ‖q‖^2 ≤ (rawSourceSquare 0/highFloor^2)*complexGram G
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hcompletion : nativeLow*‖z 0‖^2-2*‖z 0‖*‖p-q‖+
      complexGram V (fun i => (gramScales i : ℂ)*z i.succ)+
      highFloor*‖h‖^2 ≤ energy) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤ energy := by
  have hd := source_gram_domination V G hV hG (fun i => z i.succ)
  rw [scaled_gram_difference] at hd
  have hn : 0 ≤ ∑ i : Fin 3, publishedMargins i*‖z i.succ‖^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (row_margin_certificate i).2.le (sq_nonneg _))
  have hg : complexGram G (fun i => (gramScales i : ℂ)*z i.succ) ≤
      rho*complexGram V (fun i => (gramScales i : ℂ)*z i.succ) := by linarith
  have hc : 0 ≤ rawSourceSquare 0/highFloor^2 := by
    -- The original source-square upper bound is nonnegative independently of rho.
    norm_num [rawSourceSquare, highFloor]
  have hq' := source_cross_square_of_gram_domination q
    (rawSourceSquare 0/highFloor^2) rho _ _ hc hg hq
  have heq : (rawSourceSquare 0/highFloor^2)*rho = highMixedSquare := by
    unfold highMixedSquare
    ring
  rw [heq] at hq'
  have he := actual_energy_diagonal_lower z _ p q hv hp hq'
  apply physical_gap_of_native_source_bounds T x source hT hx hsource z h energy
  exact (add_le_add he (le_refl _)).trans hcompletion
