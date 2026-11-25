-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.unipotent_radical_action_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:19.427737+00:00
-- url     : https://prove2.me/submissions/ebe93acf-6c5c-49e1-83ea-6f776a905def

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_apply
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
private theorem hfe_lemma_7 (H : D.Hyp) (a b : Fin r) :
    D.h (D.f a) (D.e b) = if a = b then 1 else 0 := by
  rw [hswap_lemma_6 H (D.e b) (D.f a), H.ef b a]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]
private theorem hLsum_lemma_8 (H : D.Hyp) (g : Fin r → n → A) (y : n → A) :
    D.h (∑ i, g i) y = ∑ i, D.h (g i) y := by
  rw [hswap_lemma_6 H, hRsum_lemma_5, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hswap_lemma_6 H _ _).symm
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
theorem _root_.solution (H : D.Hyp) {Φ : (n → A) →ₗ[A] (n → A)} (hU : D.Uni Φ) (he : ∀ a, Φ (D.e a) = D.e a)
    (hP : ∀ v, Xp D v → Φ v - v ∈ Submodule.span A (Set.range D.e)) {v : n → A} (hv : Xp D v) :
    Φ v = v - ∑ a, D.h (pWp D (Φ (D.f a))) v • D.e a := by
  have hv' : ∀ a, D.h (D.e a) v = 0 := hv
  have hm := hP v hv
  rw [Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  have hΦv : Φ v = v + ∑ a, c a • D.e a := by rw [hc]; abel
  have key : ∀ b, c b = -D.h (pWp D (Φ (D.f b))) v := by
    intro b
    have hwe : ∀ a, D.h (Φ (D.f b)) (D.e a) = if b = a then 1 else 0 := by
      intro a
      rw [← he a, hU (D.f b) (D.e a), hfe_lemma_7 H]
    have hew : ∀ a, D.h (D.e a) (Φ (D.f b)) = if a = b then 1 else 0 := by
      intro a
      rw [← he a, hU (D.e a) (D.f b), H.ef]
    have hpXv : D.pXv (Φ (D.f b)) = D.f b := by
      rw [pXvap_lemma_11]
      simp [hew]
    have hpX0 : D.h (D.pX (Φ (D.f b))) v = 0 := by
      rw [pXap_lemma_10, hLsum_lemma_8 H]
      simp [h_smul_left, hv']
    have hw_v : D.h (Φ (D.f b)) v = D.h (D.f b) v + D.h (pWp D (Φ (D.f b))) v := by
      have hdec : Φ (D.f b) = D.pX (Φ (D.f b)) + D.pXv (Φ (D.f b)) + pWp D (Φ (D.f b)) := by
        rw [pWp_apply]; abel
      conv_lhs => rw [hdec]
      rw [h_add_left, h_add_left, hpX0, hpXv, zero_add]
    have hUv := hU (D.f b) v
    rw [hΦv, hRadd_lemma_2, hRsum_lemma_5, hw_v] at hUv
    simp [hRsmul_lemma_4, hwe] at hUv
    linear_combination hUv
  rw [hΦv, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [key a, neg_smul]
end PI.LevelKSplit.W.NCH
