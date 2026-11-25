-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levL_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:10.947106+00:00
-- url     : https://prove2.me/submissions/83204268-bd76-4455-953a-4f53f28e2ce3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_f_levL
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_e_levL
import Theorems.Thm_PI_LevelKSplit_W_NCL_pV_levL
import Theorems.Thm_PI_LevelKSplit_W_NCL_ext_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
variable (H : D.Hyp)
include H
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (x : n → A) : levL D 1 1 x = x := by
  apply ext_coord H
  · exact pV_levL H 1 1 x
  · intro c
    rw [h_f_levL H]
    simp [Matrix.one_apply]
  · intro c
    rw [h_e_levL H]
    simp [Matrix.one_apply]
end PI.LevelKSplit.W.NCL
