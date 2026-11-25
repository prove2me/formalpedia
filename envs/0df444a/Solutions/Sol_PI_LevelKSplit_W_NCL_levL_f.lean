-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levL_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:48:39.797392+00:00
-- url     : https://prove2.me/submissions/4ee6a19b-3ea2-449c-9ab5-c22496ee813c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Theorems.Thm_PI_LevelKSplit_W_NCL_pV_apply
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_apply
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
theorem _root_.solution (U W : Matrix (Fin r) (Fin r) A) (b : Fin r) :
    levL D U W (D.f b) = ∑ d, W d b • D.f d := by
  rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp [H.ff, H.ef]
end PI.LevelKSplit.W.NCL
