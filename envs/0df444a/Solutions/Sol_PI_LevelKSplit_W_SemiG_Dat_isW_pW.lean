-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.isW_pW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:57.949924+00:00
-- url     : https://prove2.me/submissions/39ce8951-8d82-40fc-b635-c88c605427e8

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_sub_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_e_pU
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_f_pU
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_z_pU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable (D : Dat A n r)
variable {D}
variable (D)
variable {D}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) (v : n → A) : IsW D (D.pW v) := by
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩
  · rw [pW_apply, h_sub_right, h_e_pU H, sub_self]
  · rw [pW_apply, h_sub_right, h_f_pU H, sub_self]
  · rw [pW_apply, h_sub_right, h_z_pU H, sub_self]
end PI.LevelKSplit.W.SemiG.Dat
