-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levL_sub_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:48:42.840582+00:00
-- url     : https://prove2.me/submissions/28313483-fb46-4e82-9d47-7574b4b91e04

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
theorem _root_.solution (U W : Matrix (Fin r) (Fin r) A) {v : n → A} (he : ∀ b, D.h (D.e b) v = 0) :
    levL D U W v - v ∈ Submodule.span A (Set.range D.e) := by
  have key : levL D U W v - v =
      ∑ a, (∑ b, U a b * D.h (D.f b) v) • D.e a - ∑ a, D.h (D.f a) v • D.e a := by
    rw [levL_apply, pV_apply, pX_apply_lemma_2, pXv_apply_lemma_3]
    simp only [he, mul_zero, Finset.sum_const_zero, zero_smul, sub_zero, add_zero]
    abel
  rw [key]
  exact Submodule.sub_mem _
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
end PI.LevelKSplit.W.NCL
