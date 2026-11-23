-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_e_pU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:14.029357+00:00
-- url     : https://prove2.me/submissions/80ef140c-b517-470a-8e42-ea7a761bf4bd

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_smul_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_sum_right
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
theorem _root_.solution (H : D.Hyp) (a : Fin r) (v : n → A) : D.h (D.e a) (D.pU v) = D.h (D.e a) v := by
  rw [pU_apply, pX_apply, pXv_apply, pz_apply, h_add_right, h_add_right, h_sum_right, h_sum_right]
  simp [h_smul_right, H.ee, H.ef, H.ez]
end PI.LevelKSplit.W.SemiG.Dat
