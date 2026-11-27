-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.grow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:21:04.581824+00:00
-- url     : https://prove2.me/submissions/0a5b0788-2bf3-4ef6-a9f8-5c0068b98a15

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_P_cont
import Theorems.Thm_PositivityTheory_ThKCT_Arch_sc_apply
import Theorems.Thm_PositivityTheory_ThKCT_Arch_sc_cont
import Theorems.Thm_PositivityTheory_ThKCT_Arch_bd_P
import Theorems.Thm_PositivityTheory_ThKCT_Arch_P_le
import Theorems.Thm_PositivityTheory_ThKCT_Arch_exists_P
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_shift
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_mul
import Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_smooth
import Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_bd
import Theorems.Thm_PositivityTheory_ThKCT_Arch_S_apply
import Theorems.Thm_PositivityTheory_ThKCT_Arch_shift_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
theorem _root_.solution (q : Seminorm ℂ (SchwartzMap V ℂ)) (hq : Continuous q) : ∃ (p : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ),
    Continuous p ∧ ∀ w f, q (S w f) ≤ (1 + ‖w‖) ^ M * p f := by
  obtain ⟨m, C, hC, h⟩ := exists_P q hq
  refine ⟨sc (C * 2 ^ m * 2 ^ m) (P V m), m + m, sc_cont _ (P_cont m), fun w f => (h _).trans ?_⟩
  have h1 := Bd.mul (r := 0) (A := (1 + ‖w‖) ^ m) (ph_smooth w.2 (w.2 w.1 / 2)) (shift_smooth f w.1) (fun i hi x => by
    refine (ph_bd _ _ _ _).trans ?_
    rw [pow_zero, mul_one]
    exact (pow_le_pow_left₀ (norm_nonneg _) ((norm_snd_le w).trans (by linarith)) _).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg w]) hi)) ((bd_P m f).shift w.1)
  have h2 := P_le (f := S w f) (by rw [show (S w f : V → ℂ) = _ from funext (S_apply w f)]; exact h1)
  rw [sc_apply (by positivity)]
  have h3 := norm_fst_le w
  have h4 := apply_nonneg (P V m) f
  calc _ ≤ C * (2 ^ m * ((1 + ‖w‖) ^ m * ((1 + ‖w‖) ^ m * (2 ^ m * P V m f)))) := by
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) hC
        gcongr
    _ = _ := by ring
end PositivityTheory.ThKCT.Arch
