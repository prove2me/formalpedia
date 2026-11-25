-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.h_uv_uv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:29.337237+00:00
-- url     : https://prove2.me/submissions/0afae58e-88b0-4f54-a339-fbc9306ff80c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_P2M_PI_LevelKSplit_W_NCH_h_W_e__02b956afd230
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_left
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
private theorem hRadd_lemma_2 (x y y' : n → A) : D.h x (y + y') = D.h x y + D.h x y' := by
  show (D.hL x) (y + y') = (D.hL x) y + (D.hL x) y'
  exact map_add _ _ _
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
private theorem hy1_lemma_12 {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a)) (a b : Fin r) :
    D.h (D.e b) (y a) = 0 := by
  have h1 := hy a
  unfold IsWp at h1
  exact h1.1 b
private theorem hy2_lemma_13 (H : D.Hyp) {y : Fin r → n → A} (hy : ∀ a, IsWp D (y a)) (a b : Fin r) :
    D.h (y a) (D.e b) = 0 :=
  h_W_e' H (hy a) b
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
theorem _root_.solution (a a' : Fin r) : D.h (uv D half y a) (uv D half y a') = D.h (y a) (y a') := by
  simp [uv, hRadd_lemma_2, hRsum_lemma_5, hRsmul_lemma_4, h_add_left, hLsum_lemma_8 H, h_smul_left, H.ee,
    hy1_lemma_12 hy, hy2_lemma_13 H hy]
end PI.LevelKSplit.W.NCH
