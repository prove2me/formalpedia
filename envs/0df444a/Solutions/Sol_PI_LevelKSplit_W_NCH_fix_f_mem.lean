-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.fix_f_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:52.54807+00:00
-- url     : https://prove2.me/submissions/d543e82d-11cc-4f84-b598-7eacd90a35fa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_apply
import Theorems.Thm_PI_LevelKSplit_W_NCH_xp_sub_pXv
import Theorems.Thm_PI_LevelKSplit_W_NCH_xp_e
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_isWp
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
private theorem hLap_lemma (D : Dat A n r) (x v : n → A) : D.hL x v = D.h x v := rfl
variable {D : Dat A n r}
private theorem hRsub_lemma_3 (x y y' : n → A) : D.h x (y - y') = D.h x y - D.h x y' := by
  show (D.hL x) (y - y') = (D.hL x) y - (D.hL x) y'
  exact map_sub _ _ _
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
private theorem pXap_lemma_10 (v : n → A) : D.pX v = ∑ a, D.h (D.f a) v • D.e a := by
  simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]
private theorem pXvap_lemma_11 (v : n → A) : D.pXv v = ∑ a, D.h (D.e a) v • D.f a := by
  simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, hLap_lemma]
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
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution (H : D.Hyp) (hND : ND D) {Φ : (n → A) →ₗ[A] (n → A)} (hU : D.Uni Φ)
    (hfix : ∀ v, Xp D v → Φ v = v) (a : Fin r) :
    Φ (D.f a) - D.f a ∈ Submodule.span A (Set.range D.e) := by
  obtain ⟨w, hw⟩ : ∃ w, w = Φ (D.f a) - D.f a := ⟨_, rfl⟩
  rw [← hw]
  have hv_w : ∀ v, Xp D v → D.h w v = 0 := by
    intro v hv
    have h1 := hU (D.f a) v
    rw [hfix v hv] at h1
    rw [hw, hLsub_lemma_9 H, h1, sub_self]
  have hew : ∀ b, D.h (D.e b) w = 0 := by
    intro b
    have h1 := hU (D.e b) (D.f a)
    rw [hfix (D.e b) (xp_e H b)] at h1
    rw [hw, hRsub_lemma_3, h1, sub_self]
  have hpXv : D.pXv w = 0 := by
    rw [pXvap_lemma_11]
    simp [hew]
  have hdec : w = D.pX w + pWp D w := by
    rw [pWp_apply, hpXv]; abel
  have hpX0 : ∀ v, Xp D v → D.h (D.pX w) v = 0 := by
    intro v hv
    have hv' : ∀ b, D.h (D.e b) v = 0 := hv
    rw [pXap_lemma_10, hLsum_lemma_8 H]
    simp [h_smul_left, hv']
  have hP0 : pWp D w = 0 := by
    apply hND
    intro u
    have hW := pWp_isWp H w
    unfold IsWp at hW
    obtain ⟨-, hWf⟩ := hW
    have hu : u = (u - D.pXv u) + D.pXv u := (sub_add_cancel u _).symm
    rw [hu, h_add_left]
    have hvX := xp_sub_pXv H u
    have hA : D.h (pWp D w) (u - D.pXv u) = 0 := by
      have := hv_w _ hvX
      rw [hdec, h_add_left, hpX0 _ hvX, zero_add] at this
      exact this
    have hB : D.h (u - D.pXv u) (pWp D w) = 0 := by
      rw [hswap_lemma_6 H, hA, map_zero]
    have hC : D.h (D.pXv u) (pWp D w) = 0 := by
      rw [pXvap_lemma_11, hLsum_lemma_8 H]
      simp [h_smul_left, hWf]
    rw [hB, hC, add_zero]
  rw [hdec, hP0, add_zero, pXap_lemma_10]
  exact sum_mem fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
end PI.LevelKSplit.W.NCH
