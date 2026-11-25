-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.sL_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:53.428613+00:00
-- url     : https://prove2.me/submissions/22f84fda-70a8-4672-8798-3af751690420

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_sL_eq
import Theorems.Thm_PI_LevelKSplit_W_NCH_h_tV_right
import Theorems.Thm_PI_LevelKSplit_W_NCH_h_tV_left
import Theorems.Thm_PI_LevelKSplit_W_NCH_h_tV_tV
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_left

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
private theorem hswap_lemma_6 (H : D.Hyp) (x y : n → A) : D.h y x = D.σA (D.h x y) := by
  simp only [Dat.h, Formalism.UG.hform, map_sum, map_mul, H.σσ, H.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
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
theorem _root_.solution (hh : Half D half) (x x' : n → A) : D.h (sL D half y x) (sL D half y x') = D.h x x' := by
  have e1 := h_tV_right H hy (half := half) x x'
  have e2 := h_tV_left H hy (half := half) x x'
  have e3 := h_tV_tV H hy (half := half) x x'
  rw [sL_eq, sL_eq, h_add_left, hRadd_lemma_2, hRadd_lemma_2, e1, e2, e3]
  have c1 : ∑ a, D.h (D.e a) x' * D.σA (D.h (y a) x) =
      ∑ b, D.σA (D.h (y b) x) * D.h (D.e b) x' :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  have c2 : ∑ b, D.h (y b) x' * D.σA (D.h (D.e b) x) =
      ∑ a, D.σA (D.h (D.e a) x) * D.h (y a) x' :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  have c3 : (∑ a, ∑ b, D.h (D.e a) x' * (cf D half y a b * D.σA (D.h (D.e b) x))) +
      (∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.σA (cf D half y a b) * D.h (D.e b) x')) +
      (∑ a, ∑ b, D.σA (D.h (D.e a) x) * (D.h (D.e b) x' * D.h (y a) (y b))) = 0 := by
    rw [Finset.sum_comm (f := fun a b => D.h (D.e a) x' * (cf D half y a b * D.σA (D.h (D.e b) x)))]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    simp only [cf, map_neg, map_mul, hh.sig]
    rw [← hswap_lemma_6 H (y b) (y a)]
    linear_combination (-(D.σA (D.h (D.e a) x) * D.h (D.e b) x' * D.h (y a) (y b))) * hh.two
  linear_combination c1 - c2 + c3
end PI.LevelKSplit.W.NCH
