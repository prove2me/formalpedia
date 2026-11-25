-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.lip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:29.042512+00:00
-- url     : https://prove2.me/submissions/ad7068ca-1889-4b52-87be-f649402b5e0a

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_P_cont
import Theorems.Thm_PositivityTheory_ThKCT_Arch_sc_apply
import Theorems.Thm_PositivityTheory_ThKCT_Arch_sc_cont
import Theorems.Thm_PositivityTheory_ThKCT_Arch_bd_P
import Theorems.Thm_PositivityTheory_ThKCT_Arch_P_le
import Theorems.Thm_PositivityTheory_ThKCT_Arch_exists_P
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_shift
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_shift_sub
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_mul
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_add
import Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_smooth
import Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_sub_bd
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
theorem _root_.solution (q : Seminorm ℂ (SchwartzMap V ℂ)) (hq : Continuous q) : ∃ p : Seminorm ℂ (SchwartzMap V ℂ),
    Continuous p ∧ ∀ w f, ‖w‖ ≤ 1 → q (S w f - f) ≤ ‖w‖ * p f := by
  obtain ⟨m, C, hC, h⟩ := exists_P q hq
  refine ⟨sc (C * (2 ^ m * 2 ^ (m + 1) * 2 ^ (m + 1) + 2 ^ m * 2 ^ (m + 1))) (P V (m + 1)),
    sc_cont _ (P_cont _), fun w f hw => (h _).trans ?_⟩
  have h3 := norm_fst_le w
  have hc : |w.2 w.1 / 2| ≤ ‖w‖ := by
    have := w.2.le_opNorm w.1
    rw [abs_div, abs_two, ← Real.norm_eq_abs]
    nlinarith [norm_snd_le w, norm_nonneg w.1, norm_nonneg w.2]
  have h1 := Bd.mul (m := m) ((ph_smooth w.2 (w.2 w.1 / 2)).sub contDiff_const) (shift_smooth f w.1)
    (fun i _ x => ph_sub_bd w.2 _ hw (norm_snd_le w) hc i x) ((bd_P (m + 1) f).shift w.1)
  have h2 := h1.add (((ph_smooth w.2 (w.2 w.1 / 2)).sub contDiff_const).mul (shift_smooth f w.1))
    ((shift_smooth f w.1).sub (f.smooth ⊤)) ((bd_P (m + 1) f).shift_sub (f.smooth ⊤) w.1)
  have h5 := P_le (f := S w f - f) (by
    rw [show ((S w f - f : SchwartzMap V ℂ) : V → ℂ) = _ from funext fun x => show _ =
      (ph w.2 (w.2 w.1 / 2) x - 1) * f (x + w.1) + (f (x + w.1) - f x) by rw [SchwartzMap.sub_apply, S_apply]; ring]
    exact h2)
  rw [sc_apply (by positivity)]
  have h4 := apply_nonneg (P V (m + 1)) f
  have h6 : 1 + ‖w.1‖ ≤ 2 := by linarith
  calc _ ≤ C * (2 ^ m * (‖w‖ * (2 ^ (m + 1) * (2 ^ (m + 1) * P V (m + 1) f))) + 2 ^ m * (2 ^ (m + 1) * P V (m + 1) f) * ‖w‖) := by
        refine mul_le_mul_of_nonneg_left (h5.trans ?_) hC
        gcongr
    _ = _ := by ring
end PositivityTheory.ThKCT.Arch
