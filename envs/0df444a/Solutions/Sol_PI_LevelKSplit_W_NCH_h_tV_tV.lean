-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.h_tV_tV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:32.858628+00:00
-- url     : https://prove2.me/submissions/5247b6cf-19ac-459b-8871-60da0cb6918e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_h_e_uv
import Theorems.Thm_PI_LevelKSplit_W_NCH_h_uv_e
import Theorems.Thm_PI_LevelKSplit_W_NCH_h_uv_uv
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
private theorem hRsub_lemma_3 (x y y' : n → A) : D.h x (y - y') = D.h x y - D.h x y' := by
  show (D.hL x) (y - y') = (D.hL x) y - (D.hL x) y'
  exact map_sub _ _ _
private theorem hRsmul_lemma_4 (x y : n → A) (c : A) : D.h x (c • y) = c * D.h x y := by
  show (D.hL x) (c • y) = c * (D.hL x) y
  rw [map_smul, smul_eq_mul]
private theorem hRsum_lemma_5 (x : n → A) (g : Fin r → n → A) :
    D.h x (∑ i, g i) = ∑ i, D.h x (g i) := by
  show (D.hL x) (∑ i, g i) = ∑ i, (D.hL x) (g i)
  exact map_sum _ _ _
private theorem hswap_lemma_6 (H : D.Hyp) (x y : n → A) : D.h y x = D.σA (D.h x y) := by
  simp only [Dat.h, Formalism.UG.hform, map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
private theorem hLsum_lemma_8 (H : D.Hyp) (g : Fin r → n → A) (y : n → A) :
    D.h (∑ i, g i) y = ∑ i, D.h (g i) y := by
  rw [hswap_lemma_6 H, hRsum_lemma_5, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hswap_lemma_6 H _ _).symm
private theorem hLsub_lemma_9 (H : D.Hyp) (x x' y : n → A) :
    D.h (x - x') y = D.h x y - D.h x' y := by
  rw [hswap_lemma_6 H y (x - x'), hRsub_lemma_3, map_sub, ← hswap_lemma_6 H, ← hswap_lemma_6 H]
section Sec
variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy
end Sec
end PI.LevelKSplit.W.NCH
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
variable (H : D.Hyp) {half : A} {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a))
include H hy
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution (x x' : n → A) :
    D.h (tV D half y x) (tV D half y x') =
      ∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.h (D.e b) x' * D.h (y a) (y b)) := by
  have k1 : ∀ b, D.h (D.e b) (tV D half y x') = 0 := fun b => by
    simp only [tV, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, h_e_uv H hy, H.ee, mul_zero,
      Finset.sum_const_zero, sub_self]
  have k2 : ∀ a, D.h (uv D half y a) (tV D half y x') =
      ∑ b, D.h (D.e b) x' * D.h (y a) (y b) := fun a => by
    simp only [tV, hRsub_lemma_3, hRsum_lemma_5, hRsmul_lemma_4, h_uv_uv H hy, h_uv_e H hy, mul_zero,
      Finset.sum_const_zero, sub_zero]
  rw [show tV D half y x = ∑ a, D.h (D.e a) x • uv D half y a - ∑ b, D.h (y b) x • D.e b from rfl]
  simp only [hLsub_lemma_9 H, hLsum_lemma_8 H, h_smul_left, k1, k2, mul_zero, Finset.sum_const_zero,
    sub_zero, Finset.mul_sum]
end PI.LevelKSplit.W.NCH
