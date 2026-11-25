-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levL_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:06.047433+00:00
-- url     : https://prove2.me/submissions/c667daf9-fecb-48a6-acb9-59764b02750d

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
theorem _root_.solution (U W U' W' : Matrix (Fin r) (Fin r) A) (x : n → A) :
    levL D U W (levL D U' W' x) = levL D (U * U') (W * W') x := by
  apply ext_coord H
  · rw [pV_levL H, pV_levL H, pV_levL H]
  · intro c
    simp only [h_f_levL H, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  · intro c
    simp only [h_e_levL H, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
end PI.LevelKSplit.W.NCL
