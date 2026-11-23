-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_f_pU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:14.003251+00:00
-- url     : https://prove2.me/submissions/41f28476-6d20-4bec-865a-fd8d66d841a2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_smul_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_sum_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_fe
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pX_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pXv_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pz_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_apply

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
theorem _root_.solution (H : D.Hyp) (a : Fin r) (v : n → A) : D.h (D.f a) (D.pU v) = D.h (D.f a) v := by
  rw [pU_apply, pX_apply, pXv_apply, pz_apply, h_add_right, h_add_right, h_sum_right, h_sum_right]
  simp [h_smul_right, H.ff, fe H, H.fz]
end PI.LevelKSplit.W.SemiG.Dat
