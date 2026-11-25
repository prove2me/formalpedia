-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.pV_levL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:36.883119+00:00
-- url     : https://prove2.me/submissions/4225d002-adda-4fe9-a7ce-941fb22ecb3e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Theorems.Thm_PI_LevelKSplit_W_NCL_pV_apply
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_apply
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_f_levL
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_e_levL
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
private theorem hL_apply_lemma (D : Dat A n r) (x y : n → A) : D.hL x y = D.h x y := rfl
private theorem pX_apply_lemma_2 (D : Dat A n r) (x : n → A) :
    D.pX x = ∑ a, D.h (D.f a) x • D.e a := by
  simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply_lemma]
private theorem pXv_apply_lemma_3 (D : Dat A n r) (x : n → A) :
    D.pXv x = ∑ a, D.h (D.e a) x • D.f a := by
  simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply_lemma]
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
theorem _root_.solution (U W : Matrix (Fin r) (Fin r) A) (x : n → A) :
    pV D (levL D U W x) = pV D x := by
  rw [pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp only [h_f_levL H, h_e_levL H]
  rw [levL_apply]
  abel
end PI.LevelKSplit.W.NCL
