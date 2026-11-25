-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.h_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:37.071496+00:00
-- url     : https://prove2.me/submissions/8571adbe-c00d-4240-801e-ca09c938257a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Theorems.Thm_PI_LevelKSplit_W_NCL_decomp
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_f_pV
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_e_pV
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
private theorem h_add_lemma_4 (D : Dat A n r) (v x y : n → A) : D.h v (x + y) = D.h v x + D.h v y :=
  map_add (D.hL v) x y
private theorem h_sum_lemma_6 (D : Dat A n r) (v : n → A) (t : Fin r → A) (w : Fin r → n → A) :
    D.h v (∑ a, t a • w a) = ∑ a, t a * D.h v (w a) := by
  rw [← hL_apply_lemma, map_sum]
  simp only [map_smul, smul_eq_mul, hL_apply_lemma]
private theorem h_swap_lemma_7 (D : Dat A n r) (H : D.Hyp) (x y : n → A) :
    D.h y x = D.σA (D.h x y) := by
  show (∑ i, ∑ j, D.σA (y i) * D.JA i j * x j) = D.σA (∑ i, ∑ j, D.σA (x i) * D.JA i j * y j)
  simp only [map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private theorem h_add_left_lemma_9 (D : Dat A n r) (H : D.Hyp) (x x' y : n → A) :
    D.h (x + x') y = D.h x y + D.h x' y := by
  rw [h_swap_lemma_7 D H, h_add_lemma_4, map_add, ← h_swap_lemma_7 D H, ← h_swap_lemma_7 D H]
private theorem h_sum_left_lemma_10 (D : Dat A n r) (H : D.Hyp) (t : Fin r → A) (w : Fin r → n → A)
    (y : n → A) : D.h (∑ a, t a • w a) y = ∑ a, D.σA (t a) * D.h (w a) y := by
  rw [h_swap_lemma_7 D H, h_sum_lemma_6, map_sum]
  simp only [map_mul, ← h_swap_lemma_7 D H]
variable {D : Dat A n r}
section Hyp
variable (H : D.Hyp)
include H
private theorem h_pV_e_lemma_11 (x : n → A) (a : Fin r) : D.h (pV D x) (D.e a) = 0 := by
  rw [h_swap_lemma_7 D H, h_e_pV H, map_zero]
private theorem h_pV_f_lemma_12 (x : n → A) (a : Fin r) : D.h (pV D x) (D.f a) = 0 := by
  rw [h_swap_lemma_7 D H, h_f_pV H, map_zero]
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
theorem _root_.solution (x y : n → A) :
    D.h x y = D.h (pV D x) (pV D y) + ∑ a, D.σA (D.h (D.f a) x) * D.h (D.e a) y +
      ∑ a, D.σA (D.h (D.e a) x) * D.h (D.f a) y := by
  have hx : D.h x y = D.h (pV D x) y + D.h (D.pX x) y + D.h (D.pXv x) y := by
    conv_lhs => rw [decomp D x]
    rw [h_add_left_lemma_9 D H, h_add_left_lemma_9 D H]
  have hy : D.h (pV D x) y = D.h (pV D x) (pV D y) := by
    conv_lhs => rw [decomp D y]
    rw [h_add_lemma_4, h_add_lemma_4, pX_apply_lemma_2, pXv_apply_lemma_3, h_sum_lemma_6, h_sum_lemma_6]
    simp [h_pV_e_lemma_11 H, h_pV_f_lemma_12 H]
  rw [hx, hy, pX_apply_lemma_2, pXv_apply_lemma_3, h_sum_left_lemma_10 D H, h_sum_left_lemma_10 D H]
end PI.LevelKSplit.W.NCL
