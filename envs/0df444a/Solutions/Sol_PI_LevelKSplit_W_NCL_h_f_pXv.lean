-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.h_f_pXv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:48:34.065516+00:00
-- url     : https://prove2.me/submissions/83872743-ae3d-4d4d-84d7-0c7929894cc0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
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
private theorem pXv_apply_lemma_3 (D : Dat A n r) (x : n → A) :
    D.pXv x = ∑ a, D.h (D.e a) x • D.f a := by
  simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hL_apply_lemma]
private theorem h_sum_lemma_6 (D : Dat A n r) (v : n → A) (t : Fin r → A) (w : Fin r → n → A) :
    D.h v (∑ a, t a • w a) = ∑ a, t a * D.h v (w a) := by
  rw [← hL_apply_lemma, map_sum]
  simp only [map_smul, smul_eq_mul, hL_apply_lemma]
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
theorem _root_.solution (c : Fin r) (x : n → A) : D.h (D.f c) (D.pXv x) = 0 := by
  rw [pXv_apply_lemma_3, h_sum_lemma_6]
  simp [H.ff]
end PI.LevelKSplit.W.NCL
