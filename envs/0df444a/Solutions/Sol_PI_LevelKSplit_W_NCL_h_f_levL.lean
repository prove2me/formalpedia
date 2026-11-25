-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.h_f_levL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:03:48.397262+00:00
-- url     : https://prove2.me/submissions/45fc22b0-afa8-4830-a8a8-cea0b08d3879

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_apply
import Theorems.Thm_PI_LevelKSplit_W_NCL_h_f_pV
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
private theorem h_fe_lemma_8 (D : Dat A n r) (H : D.Hyp) (a b : Fin r) :
    D.h (D.f a) (D.e b) = if b = a then 1 else 0 := by
  rw [h_swap_lemma_7 D H, H.ef]
  split_ifs <;> simp
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
theorem _root_.solution (U W : Matrix (Fin r) (Fin r) A) (c : Fin r) (x : n → A) :
    D.h (D.f c) (levL D U W x) = ∑ b, U c b * D.h (D.f b) x := by
  rw [levL_apply, h_add_lemma_4, h_add_lemma_4, h_f_pV H, h_sum_lemma_6, h_sum_lemma_6]
  simp [h_fe_lemma_8 D H, H.ff]
end PI.LevelKSplit.W.NCL
