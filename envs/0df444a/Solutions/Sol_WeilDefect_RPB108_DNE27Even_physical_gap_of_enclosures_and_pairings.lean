-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.physical_gap_of_enclosures_and_pairings
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:13:55.553562+00:00
-- url     : https://prove2.me/submissions/75b9af40-8a6b-471e-8943-0c6d45a66e8f

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_physical_gap_of_gram_and_pairings
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_retained_energy_of_enclosures
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27RetainedEnergy_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

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
    (hp : ‖p‖^2 ≤ nativeDualSquare*complexGram V
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hq : ‖q‖^2 ≤ (rawSourceSquare 0/highFloor^2)*complexGram G
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hcompletion : nativeLow*‖z 0‖^2-2*‖z 0‖*‖p-q‖+
      complexGram V (fun i => (gramScales i : ℂ)*z i.succ)+
      highFloor*‖h‖^2 ≤ energy) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤ energy := by
  exact physical_gap_of_gram_and_pairings T x source hT hx hsource V G hV hG
    z h energy p q (retained_energy_of_enclosures V hV z) hp hq hcompletion
