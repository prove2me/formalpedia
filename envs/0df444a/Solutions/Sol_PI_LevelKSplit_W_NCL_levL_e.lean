-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levL_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:31.271158+00:00
-- url     : https://prove2.me/submissions/7ae385a3-212f-46c5-8ff6-178de37c5ca2

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
theorem _root_.solution (U W : Matrix (Fin r) (Fin r) A) (b : Fin r) :
    levL D U W (D.e b) = ∑ a, U a b • D.e a := by
  rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
  simp [h_fe_lemma_8 D H, H.ee]
end PI.LevelKSplit.W.NCL
