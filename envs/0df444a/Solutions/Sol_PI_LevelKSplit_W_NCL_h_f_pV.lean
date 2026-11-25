-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.h_f_pV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:17.076677+00:00
-- url     : https://prove2.me/submissions/441317fd-bca1-43f9-8a03-3018b2c7ea52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Theorems.Thm_PI_LevelKSplit_W_NCL_pV_apply
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_f_pX
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_f_pXv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
private theorem h_sub_lemma_5 (D : Dat A n r) (v x y : n → A) : D.h v (x - y) = D.h v x - D.h v y :=
  map_sub (D.hL v) x y
variable {D : Dat A n r}
section Hyp
variable (H : D.Hyp)
include H
end Hyp
end PI.LevelKSplit.W.NCL
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
variable (H : D.Hyp)
include H
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (c : Fin r) (x : n → A) : D.h (D.f c) (pV D x) = 0 := by
  rw [pV_apply, h_sub_lemma_5, h_sub_lemma_5, h_f_pX H, h_f_pXv H]
  ring
end PI.LevelKSplit.W.NCL
