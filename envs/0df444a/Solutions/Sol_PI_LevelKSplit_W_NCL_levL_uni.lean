-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levL_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:15.173803+00:00
-- url     : https://prove2.me/submissions/c999efe2-dab5-4443-9d4b-d4b383a56524

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_f_levL
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_e_levL
import Theorems.Thm_PI_LevelKSplit_W_NCL_pV_levL
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_decomp
import Theorems.Thm_PI_LevelKSplit_W_NCL_sum_conj

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
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (H : D.Hyp) (U W : Matrix (Fin r) (Fin r) A)
    (hUW : ∀ b c, ∑ a, D.σA (U a b) * W a c = if b = c then 1 else 0)
    (hWU : ∀ b c, ∑ a, D.σA (W a b) * U a c = if b = c then 1 else 0) (x y : n → A) :
    D.h (levL D U W x) (levL D U W y) = D.h x y := by
  rw [h_decomp H (levL D U W x), h_decomp H x y, pV_levL H, pV_levL H]
  simp only [h_f_levL H, h_e_levL H]
  rw [sum_conj D.σA U W _ _ hUW, sum_conj D.σA W U _ _ hWU]
end PI.LevelKSplit.W.NCL
